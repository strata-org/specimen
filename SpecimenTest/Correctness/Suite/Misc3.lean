import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.Misc3
inductive InfiniteTree' where
  | node : InfiniteTree' → InfiniteTree' → InfiniteTree'
inductive AlwaysNode : InfiniteTree' → Prop where
  | mk : AlwaysNode l → AlwaysNode r → AlwaysNode (.node l r)
namespace Foo
inductive Bar where
| bar
inductive Baz : Bar → Prop where
| isBar : Baz .bar
end Foo
inductive Baz' : Foo.Bar → Foo.Bar → Prop where
| isBar2 : Baz' .bar .bar

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (fun (_ : Unit) => ∃ t, AlwaysNode t),
  enumerator (fun (_ : Unit) => ∃ t, AlwaysNode t),
  generator (∃ (b : Foo.Bar), Foo.Baz b),
  generator (fun a => ∃ b, Baz' a b),
  generator (fun b => ∃ a, Baz' a b),
  checker (fun a b => Baz' a b)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.Misc3
