module
public import Theory.Representation.EssentialResidualQuotient
public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.Representation.RankOne.QuadraticRecognition.Generation

/-!
# A normal Sylow seed detects the whole simple module

Let a normal subgroup K act trivially on a simple submodule I, and let
K together with a subgroup B generate a Sylow two-subgroup normalizing B.
If B acts nontrivially on I, B-fixed vectors generate the full module, and
the quotient by I is residual-fixed, then I is the whole module. A B-fixed
lift has zero K-displacement by irreducibility; odd-coset averaging then
contradicts the absence of residual-fixed vectors outside I.

Source application: the residual-section saturation argument in DGS,
Groups and Graphs (1985), Chapters 8--9, printed pp.140--142.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
namespace Representation

private theorem core_fixes_fixed_lift
    {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (I : Subrepresentation ρ)
    [I.toRepresentation.IsIrreducible]
    (K B : Subgroup H) [K.Normal] (hn : K ≤ normalizer (B : Set H))
    (hk : K ≤ I.toRepresentation.ker)
    (hB : ¬ I.toSubmodule ≤ fixedSpace ρ B)
    (v : W) (hv : v ∈ fixedSpace ρ B)
    (hlift : ∀ g, ρ g v - v ∈ I.toSubmodule) :
    v ∈ fixedSpace ρ K := by
  have hfix (k : K) (w : W) (hw : w ∈ I.toSubmodule) : ρ k w = w :=
    congrArg Subtype.val (LinearMap.congr_fun (hk k.property) (⟨w,hw⟩ : I.toSubmodule))
  let D := Submodule.span (ZMod 2) (Set.range (fun k : K => ρ k v - v))
  have hDI : D ≤ I.toSubmodule := Submodule.span_le.mpr (by rintro _ ⟨k,rfl⟩; exact hlift k)
  have hDB : D ≤ fixedSpace ρ B := Submodule.span_le.mpr (by
    rintro _ ⟨k,rfl⟩
    exact (fixedSpace ρ B).sub_mem
      ((fixedSpace_stable_of_normalizes ρ hn k.property v).2 hv) hv)
  have hD (g : H) (w : W) (hw : w ∈ D) : ρ g w ∈ D := by
    apply Submodule.span_induction (p := fun w _ => ρ g w ∈ D) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k,rfl⟩
      let k' : K := ⟨g * k * g⁻¹, (inferInstance : K.Normal).conj_mem k k.property g⟩
      have he := congrArg (ρ g) (hfix k (ρ g⁻¹ v - v) (hlift g⁻¹))
      have he' : ρ k' v - ρ g (ρ k v) = v - ρ g v := by
        simpa only [map_sub, k', map_mul, Module.End.mul_apply, ρ.self_inv_apply] using he
      have heq : ρ g (ρ k v - v) = ρ k' v - v := by
        rw [map_sub]
        apply (sub_eq_sub_iff_add_eq_add).mpr
        simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp he').symm
      rw [heq]
      exact Submodule.subset_span ⟨k',rfl⟩
    · simp only [map_zero]; exact D.zero_mem
    · intro x y _ _ hx hy
      simpa only [map_add] using D.add_mem hx hy
    · intro c x _ hx
      simpa only [map_smul] using D.smul_mem c hx
  let J : Subrepresentation I.toRepresentation := {
    toSubmodule := D.comap I.toSubmodule.subtype
    apply_mem_toSubmodule g w hw := hD g w hw }
  have hJ : J = ⊥ := by
    rcases (inferInstance : I.toRepresentation.IsIrreducible).eq_bot_or_eq_top J with h | h
    · exact h
    · exfalso
      apply hB
      intro w hw
      have hm : (⟨w,hw⟩ : I.toSubmodule) ∈ J.toSubmodule := h ▸ Submodule.mem_top
      exact hDB hm
  intro k
  have hd : ρ k v - v ∈ D := Submodule.subset_span ⟨k,rfl⟩
  have hm : (⟨ρ k v - v,hDI hd⟩ : I.toSubmodule) ∈ J.toSubmodule := hd
  rw [hJ] at hm
  have hz : ρ k v - v = 0 := congrArg Subtype.val (show (⟨_,hDI hd⟩ : I.toSubmodule) = 0 from hm)
  exact sub_eq_zero.mp hz

/-- A simple submodule is the whole space when its quotient is residual-fixed
and a normal Sylow seed generates the original space. -/
theorem constituent_eq_top_of_normal_sylow_seed
    {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) H W) (I : Subrepresentation ρ)
    [I.toRepresentation.IsIrreducible]
    (K B : Subgroup H) [K.Normal] (S : Sylow 2 H)
    (hS : K ⊔ B = S) (hn : (S : Subgroup H) ≤ normalizer (B : Set H))
    (hk : K ≤ I.toRepresentation.ker)
    (hB : ¬ I.toSubmodule ≤ fixedSpace ρ B)
    (hquot : pResidual 2 H ≤ I.quotientRepresentation.ker)
    (hzero : fixedSpace ρ (pResidual 2 H) = ⊥)
    (hgen : GeneratedByFixedSpace ρ B) : I = ⊤ := by
  have hfixed : fixedSpace ρ B ≤ I.toSubmodule := by
    by_contra hnot
    let X := (fixedSpace ρ B).map I.toSubmodule.mkQ
    have hX : X ≠ ⊥ := by
      intro he
      apply hnot
      intro w hw
      have hz : I.toSubmodule.mkQ w ∈ X := ⟨w,hw,rfl⟩
      rw [he] at hz
      exact (Submodule.Quotient.mk_eq_zero I.toSubmodule).mp hz
    have hstable : (S : Subgroup H) ≤ subspaceStabilizer I.quotientRepresentation X := by
      apply le_subspaceStabilizer
      intro s hs x hx
      obtain ⟨w,hw,rfl⟩ := hx
      exact ⟨ρ s w,(fixedSpace_stable_of_normalizes ρ hn hs w).2 hw,rfl⟩
    let : Finite (W ⧸ I.toSubmodule) := Finite.of_surjective _ I.toSubmodule.mkQ_surjective
    obtain ⟨x,hx,hxn,hxf⟩ := EssentialResidualQuotient.exists_nonzero_fixed_seed
      I.quotientRepresentation S X hstable hX
    obtain ⟨v,hv,rfl⟩ := hx
    have hlift (g : H) : ρ g v - v ∈ I.toSubmodule := by
      obtain ⟨r,hr,s,hs,rfl⟩ := mem_sup_of_normal_left.mp
        ((pResidual_sup_sylow_eq_top S).ge (mem_top g))
      apply (Submodule.Quotient.eq I.toSubmodule).mp
      change I.quotientRepresentation (r*s) (I.toSubmodule.mkQ v) = I.toSubmodule.mkQ v
      have hsf : I.quotientRepresentation s (I.toSubmodule.mkQ v) = I.toSubmodule.mkQ v := hxf ⟨s,hs⟩
      rw [map_mul,Module.End.mul_apply,hsf,hquot hr]
      rfl
    have hvK := core_fixes_fixed_lift ρ I K B
      ((show K ≤ (S : Subgroup H) from hS ▸ le_sup_left).trans hn) hk hB v hv hlift
    have hvS : v ∈ fixedSpace ρ S := by
      rw [← hS]
      change v ∈ invariants (ρ.comp (K ⊔ B).subtype)
      rw [ρ.invariants_comp_sup]
      exact ⟨hvK,hv⟩
    obtain ⟨w,hw,hvw⟩ := EssentialResidualQuotient.fixed_lift_of_displacement ρ S
      I.toSubmodule v hvS hlift
    have hw0 : w = 0 := by
      have hh : w ∈ fixedSpace ρ (pResidual 2 H) := fun r => hw r
      simpa only [hzero,Submodule.mem_bot] using hh
    rw [hw0,sub_zero] at hvw
    exact hxn ((Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr hvw)
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [←hgen]
  apply iSup_le
  intro g
  rintro _ ⟨v,hv,rfl⟩
  exact I.apply_mem_toSubmodule g (hfixed hv)

end Representation
