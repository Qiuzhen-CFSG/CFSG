module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalMarking
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The exceptional A₇ Baumann image with a fixed summand

A four-dimensional moved space and a fixed complement identify the actual
commutator subgroup [U,G] as a four-dimensional elementary normal subgroup
with the same centralizer kernel as U. Apply the exceptional A₇ theorem
to [U,G]; the Baumann image has order four. Consequently the original
Sylow cannot equal its own Baumann subgroup, since its A₇ image has order
eight. All maps are the original conjugation quotient followed by the
specified group isomorphism.

The original 13.2.12 point-action exclusion uses this to retain possible
fixed summands rather than assuming the full span is four-dimensional.
Source: Aschbacher--Smith B.2.20, C.1.24, 13.2.12, pp.82,131,882.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
variable {G : Type*} [Group G] [Finite G]

/-- A fixed complementary summand does not change the exceptional A₇
Baumann image. Apply the four-dimensional theorem to the actual commutator
subgroup, proving that it has the same action kernel as the full module. -/
theorem exceptional_baumann_image_card_of_split
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (T : Sylow 2 G) (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker)
    (hc : IsCompl (subspaceCommutator (NormalElementaryQuotient.representation U q hq hk) ⊤ ⊤)
      (fixedSpace (NormalElementaryQuotient.representation U q hq hk) ⊤))
    (hd : Module.finrank (ZMod 2)
      (subspaceCommutator (NormalElementaryQuotient.representation U q hq hk) ⊤ ⊤) = 4) :
    Nat.card ((ChapterB.baumann (T : Subgroup G)).map q) = 4 := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let W : Subgroup G := ⁅U,(⊤ : Subgroup G)⁆
  have hWU : W ≤ U := commutator_le_left _ _
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWU
  have he : NormalElementaryQuotient.commutatorSpace U (⊤ : Subgroup G) =
      subspaceCommutator ρ ⊤ ⊤ := by
    rw [NormalElementaryQuotient.commutatorSpace_eq U q hq hk,
      map_top_of_surjective q hq]
  let l := (NormalElementaryQuotient.commutatorSpaceEquiv U (⊤ : Subgroup G)).trans
    (LinearEquiv.ofEq _ _ he)
  have hdW : Module.finrank (ZMod 2) (Additive W) = 4 := l.finrank_eq.trans hd
  have hkW : q.ker = centralizer (W : Set G) := by
    apply le_antisymm (hk ▸ centralizer_le hWU)
    intro g hg
    rw [hk]
    apply mem_centralizer_iff.mpr
    intro u hu
    have hfix : ρ (q g) (Additive.ofMul (⟨u,hu⟩ : U)) = Additive.ofMul ⟨u,hu⟩ := by
      obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp
        (show Additive.ofMul (⟨u,hu⟩ : U) ∈
          subspaceCommutator ρ ⊤ ⊤ ⊔ fixedSpace ρ ⊤ from
          hc.sup_eq_top.symm ▸ Submodule.mem_top)
      have haw : (a.toMul:G) ∈ W := by
        change a ∈ NormalElementaryQuotient.commutatorSpace U (⊤ : Subgroup G)
        rw [he]
        exact ha
      have hfa : ρ (q g) a = a := by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [NormalElementaryQuotient.representation_apply]
        rw [←hg _ haw,mul_inv_cancel_right]
      have hfb : ρ (q g) b = b := hb ⟨q g,mem_top _⟩
      rw [←hab,map_add,hfa,hfb]
    have hh := congrArg (fun v : Additive U => (v.toMul:G)) hfix
    rw [NormalElementaryQuotient.representation_apply] at hh
    change g * u * g⁻¹ = u at hh
    exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
  obtain ⟨A,_,hA,_,hBA⟩ := exceptional_thompson_baumann_images W q hq hkW hdW T
    (hWU.trans hUT) hJ
  rw [hBA]
  exact (BinaryAlternatingSevenControl.best_dimensions
    (NormalElementaryQuotient.representation W q hq hkW)
    (NormalElementaryQuotient.representation_injective W q hq hkW) hdW hA).2.1

/-- The exceptional A₇ module cannot occur when the original Sylow is
itself a Baumann subgroup. This transports through the supplied quotient
isomorphism and retains the fixed summand of the original module. -/
theorem exceptional_not_baumann_sylow_of_split
    {E : Type*} [Group E] [Finite E]
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* E) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (e : E ≃* alternatingGroup (Fin 7))
    (T : Sylow 2 G) (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker)
    (hB : ChapterB.baumann (T : Subgroup G) = (T : Subgroup G))
    (hc : IsCompl (subspaceCommutator (NormalElementaryQuotient.representation U q hq hk) ⊤ ⊤)
      (fixedSpace (NormalElementaryQuotient.representation U q hq hk) ⊤))
    (hd : Module.finrank (ZMod 2)
      (subspaceCommutator (NormalElementaryQuotient.representation U q hq hk) ⊤ ⊤) = 4) :
    False := by
  let q' := e.toMonoidHom.comp q
  have hq' : Function.Surjective q' := e.surjective.comp hq
  have hker : q'.ker = q.ker := by
    ext g
    change e (q g) = 1 ↔ q g = 1
    exact e.map_eq_one_iff
  have hk' : q'.ker = centralizer (U : Set G) := hker.trans hk
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let σ := NormalElementaryQuotient.representation U q' hq' hk'
  have he : σ.comp e.toMonoidHom = ρ := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    obtain ⟨g,rfl⟩ := hq g
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((σ (q' g) v).toMul:G) = ((ρ (q g) v).toMul:G)
    rw [NormalElementaryQuotient.representation_apply,
      NormalElementaryQuotient.representation_apply]
  have hm : subspaceCommutator ρ ⊤ ⊤ = subspaceCommutator σ ⊤ ⊤ := by
    rw [←he,subspaceCommutator_comp_map,map_top_of_surjective _ e.surjective]
  have hf : fixedSpace ρ ⊤ = fixedSpace σ ⊤ := by
    rw [←he,fixedSpace_comp_map,map_top_of_surjective _ e.surjective]
  have hcard := exceptional_baumann_image_card_of_split U q' hq' hk' T hUT
    (by rwa [hker]) (by
      change IsCompl (subspaceCommutator σ ⊤ ⊤) (fixedSpace σ ⊤)
      rw [←hm,←hf]
      exact hc) (by
      change Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ ⊤) = 4
      rw [←hm]
      exact hd)
  rw [hB] at hcard
  let P := T.mapSurjective hq'
  have hP : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_eq_fintype_card]
    norm_num [Nat.factorial]
    rw [show (2520 : ℕ).factorization 2 = 3 by
      rw [show 2520 = 2^3*315 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]]
    norm_num
  change Nat.card P = 4 at hcard
  omega
end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
