module
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# Fixed factors under an involution

A fixed element in a product of invariant subgroups has a defect in their
intersection. If the elementary intersection has vanishing first cohomology,
correcting one factor by a coboundary gives two fixed factors. The identity
is used for Q and Qˣ in the nontrivial-center branch of Aschbacher–Smith
2.4.21, printed p.536.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G]
open scoped Pointwise

theorem fixed_sup_of_intersection_coboundaries
    (U V : Subgroup G) (hVU : V ≤ normalizer (U : Set G))
    (α : G →* G) (hα : Function.Involutive α)
    (hU : ∀ u ∈ U, α u ∈ U) (hV : ∀ v ∈ V, α v ∈ V)
    (hW2 : ∀ w ∈ U ⊓ V, w^2=1)
    (hW : ∀ w ∈ U ⊓ V, α w=w → ∃ z ∈ U ⊓ V, w=z*(α z)⁻¹) :
    (U ⊔ V) ⊓ α.eqLocus (MonoidHom.id G) =
      (U ⊓ α.eqLocus (MonoidHom.id G)) ⊔ (V ⊓ α.eqLocus (MonoidHom.id G)) := by
  let F := α.eqLocus (MonoidHom.id G)
  apply le_antisymm
  · rintro r ⟨hr,hrf⟩
    have hp : r ∈ (U:Set G)*(V:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left U V hVU]
      exact hr
    obtain ⟨u,hu,v,hv,rfl⟩ := hp
    have he : α u*α v=u*v := by
      change α (u*v)=u*v at hrf
      simpa only [map_mul] using hrf
    let d := u⁻¹*α u
    have hdU : d ∈ U := U.mul_mem (U.inv_mem hu) (hU u hu)
    have hdV : d ∈ V := by
      have hd : d=v*(α v)⁻¹ := by
        calc
          d = u⁻¹*(α u*α v)*(α v)⁻¹ := by dsimp only [d]; group
          _ = v*(α v)⁻¹ := by rw [he]; group
      exact hd ▸ V.mul_mem hv (V.inv_mem (hV v hv))
    have hdf : α d=d := by
      have hi : d⁻¹=d := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hW2 d ⟨hdU,hdV⟩)
      calc
        α d = d⁻¹ := by
          dsimp only [d]
          rw [map_mul,map_inv,hα u,mul_inv_rev,inv_inv]
        _ = d := hi
    obtain ⟨w,hw,hd⟩ := hW d ⟨hdU,hdV⟩ hdf
    have huf : α (u*w)=u*w := by
      rw [map_mul]
      calc
        α u*α w = u*d*α w := by dsimp only [d];group
        _ = u*w := by rw [hd];group
    have huv : (u*w)*(w⁻¹*v)=u*v := by group
    have hvf : α (w⁻¹*v)=w⁻¹*v := by
      apply mul_left_cancel (a := u*w)
      conv_lhs => rw [←huf,←map_mul,huv,map_mul,he]
      exact huv.symm
    have hu' : u*w ∈ U ⊓ F := ⟨U.mul_mem hu hw.1,huf⟩
    have hv' : w⁻¹*v ∈ V ⊓ F := ⟨V.mul_mem (V.inv_mem hw.2) hv,hvf⟩
    change u*v ∈ (U ⊓ F) ⊔ (V ⊓ F)
    rw [←huv]
    exact ((U ⊓ F) ⊔ (V ⊓ F)).mul_mem
      ((show U ⊓ F ≤ _ from le_sup_left) hu') ((show V ⊓ F ≤ _ from le_sup_right) hv')
  · exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)
end Subgroup
