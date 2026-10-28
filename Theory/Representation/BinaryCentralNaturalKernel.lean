module

public import Theory.Representation.CentralKernelCohomology
public import Theory.Representation.BinaryParabolicNatural.CentralCovers
public import Theory.Representation.FirstCohomologyDuality.QuotientGeometry
public import Theory.Representation.ElementaryPerfectSplit

/-!
# The full kernel on a binary natural central extension

A normal subgroup carries the full natural quotient action. When its
quotient-action kernel fixes the whole elementary module, dual H1
vanishing splits the central kernel from its literal commutator space.
Normality preserves that space under the whole actor. Consequently the
whole quotient-action kernel fixes the original whole module as well.

Source: Aschbacher--Smith 12.7.16 and I.1.6, printed pp.844 and408.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Representation
open OneCohomology BinaryParabolicNatural BinaryLinear.OuterCyclic
variable {G : Type*} [Group G]

/-- The same quotient action detects the full elementary action once its
normal full-image actor descends, in binary dimension at least four. -/
theorem kernel_fixes_of_normal_full_natural_central_section
    {n : ℕ} (hn : 4≤n) (W B : Subgroup G) [W.Normal] [B.Normal] [IsElementaryAbelian 2 W]
    (π : W →* Multiplicative (Space n)) (hπ : Function.Surjective π)
    (hk : ∀ w : W, π w=1 → (w:G)∈center G)
    (r : G →* LinearGroup n) (hB : B.map r=⊤)
    (heq : ∀ (g : G) (w : W),
      (π ((MulAut.conjNormal g : MulAut W) w)).toAdd=r g (π w).toAdd)
    (hBk : (r.comp B.subtype).ker≤
      ((MulAut.conjNormal : G →* MulAut W).comp B.subtype).ker) :
    r.ker≤centralizer (W : Set G) := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n=>(g : Space n → Space n)) DFunLike.coe_injective
  let α : G →* MulAut W := MulAut.conjNormal
  let q := r.comp B.subtype
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨b,hb,hba⟩ := (show a∈B.map r from hB.symm ▸ mem_top a)
    exact ⟨⟨b,hb⟩,hba⟩
  let β : LinearGroup n →* MulAut W := q.liftOfSurjective hq ⟨α.comp B.subtype,hBk⟩
  have hβ (b : B) : β (q b)=α b := q.liftOfRightInverse_comp_apply
    (Function.surjInv hq) (Function.rightInverse_surjInv hq) ⟨α.comp B.subtype,hBk⟩ b
  let σ := elementaryRepresentation (p:=2) β
  let τ := elementaryRepresentation (p:=2) α
  have hσ (b : B) (v : Additive W) : σ (q b) v=τ b v := by
    change Additive.ofMul (β (q b) v.toMul)=Additive.ofMul (α b v.toMul)
    rw [hβ]
  let pl : Additive W →+ Space n := {
    toFun := fun v=>(π v.toMul).toAdd
    map_zero' := π.map_one
    map_add' := π.map_mul }
  let p : σ.IntertwiningMap (natural (Space n)) := {
    toLinearMap := pl.toZModLinearMap 2
    isIntertwining' := by
      intro a
      apply LinearMap.ext
      intro v
      obtain ⟨b,rfl⟩ := hq a
      change (π (σ (q b) v).toMul).toAdd=q b (π v.toMul).toAdd
      rw [hσ]
      exact heq b v.toMul }
  have hp : Function.Surjective p := by
    intro v
    obtain ⟨w,hw⟩ := hπ (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul w,congrArg Multiplicative.toAdd hw⟩
  have hpk : p.toLinearMap.ker≤σ.invariants := by
    intro v hv a
    obtain ⟨b,rfl⟩ := hq a
    rw [hσ]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (b:G)*(v.toMul:G)*(b:G)⁻¹=(v.toMul:G)
    exact mul_inv_eq_of_eq_mul (mem_center_iff.mp (hk v.toMul hv) b)
  let : Subsingleton (H1 (natural (Space n)).dual) :=
    (Module.finrank_eq_zero_iff_of_free (ZMod 2) _).mp (dual_H1_zero hn)
  have hdis := central_kernel_disjoint_commutator p hp hpk
  let D := Coinvariants.ker σ
  have hsup : D⊔p.toLinearMap.ker=⊤ := by
    have hm := map_coinvariants_of_surjective p hp
    rw [natural_coinvariants (by simpa [Space] using le_trans (by decide : 2≤4) hn)] at hm
    have hh := congrArg (Submodule.comap p.toLinearMap) hm
    simpa only [Submodule.comap_map_eq,Submodule.comap_top] using hh
  have hDstable (g : G) (v : Additive W) (hv : v∈D) : τ g v∈D := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨a,w⟩,rfl⟩ := hv
      obtain ⟨b,rfl⟩ := hq a
      let b' : B := ⟨g*b*g⁻¹,(inferInstance : B.Normal).conj_mem b b.property g⟩
      have he : τ g (σ (q b) w-w)=σ (q b') (τ g w)-τ g w := by
        rw [map_sub,hσ,hσ]
        have hh : τ g (τ b w)=τ (b':G) (τ g w) := by
          rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
          congr 2
          change g*(b:G)=(g*b*g⁻¹)*g
          group
        rw [hh]
      rw [he]
      exact Coinvariants.sub_mem_ker (q b') (τ g w)
    | zero => rw [map_zero]; exact D.zero_mem
    | add v w hv hw ihv ihw => rw [map_add]; exact D.add_mem ihv ihw
    | smul c v hv ih => rw [map_smul]; exact D.smul_mem c ih
  intro g hg
  have hfix (v : Additive W) : τ g v=v := by
    have hv : v∈D⊔p.toLinearMap.ker := hsup.symm ▸ Submodule.mem_top
    obtain ⟨d,hd,k,hk0,rfl⟩ := Submodule.mem_sup.mp hv
    have hkfix : τ g k=k := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change g*(k.toMul:G)*g⁻¹=(k.toMul:G)
      exact mul_inv_eq_of_eq_mul (mem_center_iff.mp (hk k.toMul hk0) g)
    have hdfix : τ g d=d := by
      apply sub_eq_zero.mp
      apply Submodule.disjoint_def.mp hdis
      · exact D.sub_mem (hDstable g d hd) hd
      · change p (τ g d-d)=0
        rw [map_sub]
        change (π ((MulAut.conjNormal g : MulAut W) d.toMul)).toAdd-(π d.toMul).toAdd=0
        rw [heq,hg]
        exact sub_self _
    rw [map_add,hkfix,hdfix]
  intro w hw
  have hh := congrArg (fun v : Additive W=>(v.toMul:G)) (hfix (Additive.ofMul ⟨w,hw⟩))
  change g*w*g⁻¹=w at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end Representation
