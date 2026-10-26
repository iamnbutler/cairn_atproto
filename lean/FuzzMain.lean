import FakeApp
import Cairn.Fuzz.Collect
import Cairn.Fuzz.Main

/-! `lake exe fuzz [<target>] …` (`cairn fuzz`): Cairn's claim-driven fuzzer on this package's
machines: `FakeApp` through the runtime with the fake PDS as its server (lean/FakeApp.lean), and
`Claims`, the session machine's harness, at the model level. -/

def targets : List Cairn.Fuzz.Target := fuzz_targets%

def main (args : List String) : IO UInt32 := Cairn.Fuzz.main targets args
