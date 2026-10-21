import Specimen.DeriveConstrainedProducer
import Plausible.Attr
import Specimen.Basalt

/-! Tests for `derive_generator` command syntax variations and namespace handling. -/

set_option guard_msgs.diff true

namespace Foo

inductive Bar where
| bar

inductive Baz : Bar → Prop where
| isBar : Baz .bar

end Foo

--

#guard_msgs(warning, drop info) in
derive_generator (∃ (b: Foo.Bar), Foo.Baz b)


section

open Foo

#guard_msgs(warning, drop info) in
derive_generator (∃ (b: Bar), Baz b)


inductive Baz' : Bar → Bar → Prop where
| isBar2 : Baz' .bar .bar

-- `Bar` has one constructor, so matching the input against `.bar` cannot fail and emits no failure arm.
#guard_msgs(warning, drop info) in
derive_generator (fun a => ∃ b, Baz' a b)

end
