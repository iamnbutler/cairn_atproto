module

public import CairnAtproto.Acts
public import CairnAtproto.Proofs.RoundTrip

/-! # Acting: round trips, the same write, and how a write's reply is read

* `ofJson (toJson v) = v` for the records, writes, `getRecord`'s view, the detailed profile,
  notifications and `getPosts`' answer.
* `Call.putRecord_same`: a `putRecord` call reads back as the write it was built from, so the
  same write is the same request (`cairn_atproto^20`).
* `WriteOutcome.ofReply_*`: 2xx acked, other statuses below 500 refused, 5xx, timeouts and network
  failures lost (`cairn_atproto^21`). -/

@[expose] public section

namespace CairnAtproto
open CairnJson

theorem Record.ofJson_toJson (r : Record) : Record.ofJson r.toJson = r := by
  cases r with
  | like s at_ =>
    simp [Record.ofJson, Record.toJson, Json.type, Json.obj?, Json.str?, Json.field, List.find?,
      Json.getStr, StrongRef.ofJson_toJson]
  | repost s at_ =>
    simp [Record.ofJson, Record.toJson, Json.type, Json.obj?, Json.str?, Json.field, List.find?,
      Json.getStr, StrongRef.ofJson_toJson, nsidLike, nsidRepost]
  | follow d at_ =>
    simp [Record.ofJson, Record.toJson, Json.type, Json.str?, Json.field, List.find?,
      Json.getStr, nsidLike, nsidRepost, nsidFollow]
  | other t =>
    simp [Record.ofJson, Record.toJson, type_lone, Json.obj?, Json.str?, Json.field, List.find?]

@[simp] theorem Record.asObj_toJson (r : Record) : Json.asObj r.toJson = some r.toJson := by
  cases r <;> rfl

theorem PutRecord.ofJson_toJson (w : PutRecord) : PutRecord.ofJson w.toJson = some w := by
  obtain ⟨repo, rkey, record⟩ := w
  simp [PutRecord.ofJson, PutRecord.toJson, Json.obj?, Json.str?, Json.field, List.find?,
    Json.getStr, Record.ofJson_toJson]

theorem deleteRecordOf_json (u : AtUri) : deleteRecordOf (deleteRecordJson u) = some u := by
  obtain ⟨r, c, k⟩ := u
  simp [deleteRecordOf, deleteRecordJson, Json.str?, Json.field, List.find?, Json.getStr]

theorem RecordView.ofJson_toJson (r : RecordView) : RecordView.ofJson r.toJson = some r := by
  obtain ⟨uri, cid, value⟩ := r
  cases cid <;>
    simp [RecordView.ofJson, RecordView.toJson, opt, Json.obj?, Json.str?, Json.field, List.find?,
      Json.getStr, Record.ofJson_toJson]

theorem ProfileDetail.ofJson_toJson (d : ProfileDetail) : ProfileDetail.ofJson d.toJson = some d := by
  obtain ⟨⟨did, handle, dn, av, v⟩, desc, a, b, c⟩ := d
  rcases nonDefault_cases {} v with ⟨h, rfl⟩ | h <;> cases dn <;> cases av <;> cases desc <;>
    simp [h, ProfileDetail.ofJson, ProfileDetail.toJson, Profile.ofJson, Profile.toJson,
      ProfileViewer.of, opt, Json.obj?, Json.str?, Json.nat?, Json.asNat, Json.ofNat, Json.field,
      List.find?, Json.getStr, ProfileViewer.ofJson_toJson]

theorem NotificationReason.toString_ofString (s : String) :
    (NotificationReason.ofString s).toString = s := by
  unfold NotificationReason.ofString
  split <;> rfl

theorem Notification.ofJson_toJson (n : Notification) (h : n.reason.Canonical) :
    Notification.ofJson n.toJson = some n := by
  obtain ⟨uri, cid, author, reason, rs, text, isRead, indexedAt⟩ := n
  simp only [NotificationReason.Canonical] at h
  cases rs <;> cases text <;>
    simp [h, Notification.ofJson, Notification.toJson, opt, Json.obj?, Json.str?, Json.bool?,
      Json.field, List.find?, Json.getStr, Json.getBool, Profile.ofJson_toJson]

@[simp] theorem Notification.asObj_toJson (n : Notification) :
    Json.asObj n.toJson = some n.toJson := rfl

theorem NotificationPage.ofJson_toJson (p : NotificationPage)
    (h : ∀ n ∈ p.notifications, n.reason.Canonical) :
    NotificationPage.ofJson p.toJson = some p := by
  obtain ⟨ns, cursor, seenAt⟩ := p
  have hm := optMap_map Notification.ofJson Notification.toJson ns
    (fun n hn => Notification.ofJson_toJson n (h n hn))
  cases cursor <;> cases seenAt <;>
    simp [NotificationPage.ofJson, NotificationPage.toJson, opt, Json.arr?, Json.str?, Json.field,
      List.find?, Json.getArr, Json.getStr, hm]

theorem Posts.ofJson_toJson (p : Posts) : Posts.ofJson p.toJson = some p := by
  obtain ⟨ps⟩ := p
  simp [Posts.ofJson, Posts.toJson, Json.arr?, Json.field, List.find?, Json.getArr,
    optMap_map Post.ofJson Post.toJson ps (fun q _ => Post.ofJson_toJson q)]

theorem unreadCountOf_json (n : Nat) : unreadCountOf (unreadCountJson n) = some n := by
  simp [unreadCountOf, unreadCountJson, Json.nat?, Json.field, List.find?, Json.asNat, Json.ofNat]

theorem seenAtOf_json (s : String) : seenAtOf (seenAtJson s) = some s := by
  simp [seenAtOf, seenAtJson, Json.str?, Json.field, List.find?, Json.getStr]

/-! ## The same write is the same request -/

/-- **A `putRecord` call is built from the write alone**: a POST to `putRecord` whose body is
the write's JSON, which reads back as the write. So the same key and record make the same
request, and a server sees the same write (through text, `Session.Call.putRecordOf_putRecord`
in `CairnAtprotoProofs.Text`). -/
theorem Session.Call.putRecord_body (w : PutRecord) :
    (Session.Call.putRecord w).nsid = nsidPutRecord ∧ (Session.Call.putRecord w).procedure = true ∧
      (Session.Call.putRecord w).body = encode w.toJson ∧ PutRecord.ofJson w.toJson = some w :=
  ⟨rfl, rfl, rfl, PutRecord.ofJson_toJson w⟩

/-! ## How a write's reply is read -/

theorem WriteOutcome.ofReply_success (st : Nat) (hs : 200 ≤ st ∧ st < 300) hs' b :
    WriteOutcome.ofReply (.http st hs' b) = .acked := by
  simp [WriteOutcome.ofReply, isSuccess, hs.1, hs.2]

theorem WriteOutcome.ofReply_refused (st : Nat) (hs : ¬(200 ≤ st ∧ st < 300)) (h5 : st < 500)
    hs' b : WriteOutcome.ofReply (.http st hs' b) =
      .refused st (XrpcError.ofBody b) (ratelimitReset hs') := by
  have : isSuccess st = false := by simp only [isSuccess]; grind
  simp [WriteOutcome.ofReply, this, h5]

theorem WriteOutcome.ofReply_server (st : Nat) (h5 : 500 ≤ st) hs' b :
    WriteOutcome.ofReply (.http st hs' b) = .lost (.server st) := by
  have : isSuccess st = false := by simp only [isSuccess]; grind
  simp [WriteOutcome.ofReply, this, Nat.not_lt.2 h5]

/-- What `cairn_atproto^21` claims: a write's reply is read as acknowledged exactly on a 2xx,
refused on any other status below 500 (with the error and the rate limit's reset), and lost on
a 5xx, a timeout or a network failure; a request the host never sent (a missing Keychain item)
is not applied. -/
def WriteReading : Prop :=
  (∀ st hs b, WriteOutcome.ofReply (.http st hs b) = .acked ↔ 200 ≤ st ∧ st < 300) ∧
  (∀ st hs b, ¬(200 ≤ st ∧ st < 300) → st < 500 →
    WriteOutcome.ofReply (.http st hs b) = .refused st (XrpcError.ofBody b) (ratelimitReset hs)) ∧
  (∀ st hs b, 500 ≤ st → WriteOutcome.ofReply (.http st hs b) = .lost (.server st)) ∧
  (∀ m, WriteOutcome.ofReply (.failed .timeout m) = .lost .timeout) ∧
  (∀ m, WriteOutcome.ofReply (.failed .network m) = .lost .network) ∧
  (∀ m, WriteOutcome.ofReply (.failed .notFound m) = .notSent) ∧
  WriteOutcome.ofAnswer .signedOut = .notSent

theorem writeReading : WriteReading := by
  refine ⟨fun st hs b => ⟨fun h => ?_, fun h => WriteOutcome.ofReply_success st h hs b⟩,
    fun st hs b h h5 => WriteOutcome.ofReply_refused st h h5 hs b,
    fun st hs b h5 => WriteOutcome.ofReply_server st h5 hs b,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  refine Classical.byContradiction fun hn => ?_
  by_cases h5 : st < 500
  · rw [WriteOutcome.ofReply_refused st hn h5] at h; cases h
  · rw [WriteOutcome.ofReply_server st (Nat.le_of_not_lt h5)] at h; cases h

end CairnAtproto
