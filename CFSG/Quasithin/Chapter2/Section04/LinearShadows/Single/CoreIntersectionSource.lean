module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.TorusIntervalSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CoreCenterSource
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# Involutions in the intersection with the maximal-local core

The odd torus leaves no subgroup strictly between Z and the elementary
module. If R is not contained in O₂(M), each of its two elementary factors
therefore intersects the core in Z. Their involution covering gives
Ω₁(R ∩ O₂(M)) = Z.

Source: Aschbacher–Smith, the centerless branch of 2.4.18, printed p.534.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- If R is not in O₂(M), the only involutions in their intersection lie
in Z(R). This is the invariant-subgroup step of original 2.4.18. -/
theorem source_centerless_core_intersection_omega
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) = ⊥)
    (hRP : ¬ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤ twoCore M) :
    omegaOneAmbient (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓ twoCore M) =
      distinguishedZ d := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let U := sourceModule (d.block.map d.H.subtype)
  let Z := distinguishedZ d
  let P := twoCore M
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  let e := MulAut.conj x⁻¹
  let V := U.map e.toMonoidHom
  have hpair := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS
  have hPe : P.map e.toMonoidHom = P := mem_normalizer_iff_map_conj_eq.mp
    (le_normalizer_twoCore M (hTM (T.inv_mem hxT)))
  have hZe : Z.map e.toMonoidHom = Z := mem_normalizer_iff_map_conj_eq.mp
    (source_distinguished_normalized_by_sylow d hG T hST hsingle hL hz (T.inv_mem hxT))
  have hUP : ¬ U ≤ P := by
    intro hUP
    apply hRP
    rw [hpair.1]
    exact sup_le hUP ((map_mono hUP).trans_eq hPe)
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  let : IsElementaryAbelian 2 Z := hb.1
  have hZP : Z ≤ P :=
    (source_centerless_distinguished_core_center d hG T hST hsingle hL hM hTM hunique hz).1.trans inf_le_left
  have hZU : Z ≤ U := hb.2.2.1.trans
    ((source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).ge.trans inf_le_left)
  obtain ⟨D,B,hDM,hDB,_,hcard,_,hodd,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ :=
    source_fixed_free_torus d hG T hST hsingle hL hM hTM hunique
  have hDU : D ≤ normalizer (U : Set G) := (hDM.trans inf_le_right).trans
    ((d.block.map d.H.subtype).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (ChapterC.blockU (d.block.map d.H.subtype))))
  have hDN : D ≤ normalizer ((U ⊓ P : Subgroup G) : Set G) :=
    (le_inf hDU ((hDM.trans inf_le_left).trans (le_normalizer_twoCore M))).trans
      inf_normalizer_le_normalizer_inf
  have hNP : U ⊓ P = Z := by
    rcases source_centerless_torus_invariant_interval d hG T hST hsingle hL hM hTM hunique hz
      D (U ⊓ P) (hDM.trans inf_le_right) (hodd.of_dvd_nat (card_dvd_of_le hDB)) hcard
      hDN (le_inf hZU hZP) inf_le_left with he | he
    · exact he
    · exact False.elim (hUP (he.symm.le.trans inf_le_right))
  have hVP : V ⊓ P = Z := by
    have he := congrArg (map e.toMonoidHom) hNP
    rw [map_inf _ _ _ e.injective,hPe,hZe] at he
    exact he
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro a ha ha2
    rcases (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).1 a ha.1 ha2 with hu | hv
    · exact hNP.le ⟨hu,ha.2⟩
    · exact hVP.le ⟨hv,ha.2⟩
  · intro a ha
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl a
      ⟨(hb.2.2.1.trans inf_le_left) ha,hZP ha⟩ (elemPow_eq_one_of_isElementaryAbelian a ha)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
