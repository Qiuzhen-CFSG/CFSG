module
public import Theory.GroupTheory.QuaternionCentralProductTransport
import all Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# The actual factors of a transported quaternion central product

These projection identities expose the marked factor images of the existing
transport, without exposing its implementation to downstream consumers. The
source application identifies the original quaternion normalizer in the three
overgroups of Q in Aschbacher–Smith 13.9.8(2), printed p.972 (PDF p.989).
-/

namespace Subgroup.QuaternionCentralProductData
variable {G H : Type*} [Group G] [Group H]

private theorem map_left_impl (d : QuaternionCentralProductData G) (e : G≃*H) :
    (d.map e).left=d.left.map e.toMonoidHom := rfl

private theorem map_right_impl (d : QuaternionCentralProductData G) (e : G≃*H) :
    (d.map e).right=d.right.map e.toMonoidHom := rfl
public theorem map_left (d : QuaternionCentralProductData G) (e : G≃*H) :
    (d.map e).left=d.left.map e.toMonoidHom := map_left_impl d e

public theorem map_right (d : QuaternionCentralProductData G) (e : G≃*H) :
    (d.map e).right=d.right.map e.toMonoidHom := map_right_impl d e
end Subgroup.QuaternionCentralProductData
