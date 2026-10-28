module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CubicTerminal.CoreSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CubicTerminal.NineSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingPreparationKnownSimple
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SplitPrimeTorusSource
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.EquivariantMark
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CubicTerminal.InvariantAmbient

/-!
# The exceptional cubic terminal contradiction

The actual torus actor constructs the original common E₉. Frattini
rechooses the crossing to normalize that same E₉ while preserving the
component conjugate. The original displaced core remains fixed throughout:
it is its cubic commutator, lies in the component Sylow, and is
non-elementary by the first source Frattini argument. Equivariant rigidity
makes it the entire component Sylow. The conjugate cubic actor then
centralizes this Sylow, contradicting the three-prime action kernel.

The preceding component action is retained here and constructed internally
by CubicTerminal.Complete. Source: Aschbacher--Smith 2.5.7, printed p.556.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher Matrix.PSL3Four.RootNormalizerModel
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

omit [Finite G] in
private theorem cubic_map_centralizer (K : Subgroup G) (a : G) :
    (centralizer (K : Set G)).conjBy a = centralizer (K.conjBy a : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro u hu
    let f := MulAut.conj a
    refine ⟨f.symm u, ?_, f.apply_symm_apply u⟩
    intro k hk
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using hu (f k) (mem_map_of_mem _ hk)

theorem MathieuSourceSetup.linear_four_terminal_of_component_action
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (e : L ⧸ center L ≃* Matrix.PSL3Four.PSL)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype) :
    let U := (S : Subgroup H).map H.subtype
    let D := ⁅U ⊓ L, U ⊓ L⁆
    let R := elementaryAbelianMaxJ U
    let N := pairNormalizer D R x⁻¹
    D.conjBy x⁻¹ ≤ centralizer (L : Set G) →
    ∀ (P : Sylow 2 L), (P : Subgroup L).map L.subtype = U ⊓ L →
    ∀ (hNL : N ≤ normalizer (L : Set G)) (α : N →* MulAut Matrix.PSL3Four.PSL),
      (∀ n k, α n (e (QuotientGroup.mk' (center L) k)) =
        e (QuotientGroup.mk' (center L) (L.normalizerMonoidHom ⟨n, hNL n.property⟩ k))) →
      (∀ n, ((P.mapSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' (center L)))
        (e.surjective.comp (QuotientGroup.mk'_surjective _))) : Subgroup Matrix.PSL3Four.PSL).map
          (α n).toMonoidHom = P.mapSurjective
            (f := e.toMonoidHom.comp (QuotientGroup.mk' (center L)))
            (e.surjective.comp (QuotientGroup.mk'_surjective _))) →
      Nat.Coprime 3 (Nat.card α.ker) → False := by
  dsimp only
  intro hDx P hP hNL α hα hαP hαker
  let U := (S : Subgroup H).map H.subtype
  let SK := U ⊓ L
  let D := ⁅SK, SK⁆
  let R := elementaryAbelianMaxJ U
  let C := R ⊓ twoCore H
  let Q := C.conjBy x⁻¹
  let N := pairNormalizer D R x⁻¹
  change D.conjBy x⁻¹ ≤ centralizer (L : Set G) at hDx
  change (P : Subgroup L).map L.subtype = SK at hP
  change N ≤ normalizer (L : Set G) at hNL
  let := MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple
    hempty Matrix.PSL3Four.F (by decide : 1 < 2) (by simpa using Matrix.PSL3Four.card_F) e
  have hUL : U ≤ normalizer (L : Set G) :=
    (map_subtype_le _).trans
      ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have hUSK : U ≤ normalizer (SK : Set G) :=
    (le_inf U.le_normalizer hUL).trans inf_normalizer_le_normalizer_inf
  have hxD : x ^ 2 ∈ normalizer (D : Set G) :=
    normalizer_le_normalizer_derived SK (hUSK hx2)
  have hxDinv : (x⁻¹) ^ 2 ∈ normalizer (D : Set G) := by
    rw [inv_pow]
    exact (normalizer (D : Set G)).inv_mem hxD
  have hxR : x ∈ normalizer (R : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change R.map (MulAut.conj x).toMonoidHom = R
    rw [← elementaryAbelianMaxJ_map_injective _ (MulAut.conj x).injective]
    have hm : U.map (MulAut.conj x).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp hxN
    rw [hm]
  have hRx : R.conjBy x⁻¹ = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hxR)
  have hxNN : x⁻¹ ∈ normalizer (N : Set G) :=
    mem_normalizer_pairNormalizer D R x⁻¹ hxDinv ((normalizer (R : Set G)).inv_mem hxR)
  have hNLx : N ≤ normalizer (L.conjBy x⁻¹ : Set G) := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hNL
    rw [map_equiv_normalizer_eq] at hh
    change N.conjBy x⁻¹ ≤ _ at hh
    have he : N.conjBy x⁻¹ = N := mem_normalizer_iff_map_conj_eq.mp hxNN
    rwa [he] at hh
  have hRU : R ≤ U := sSup_le fun _ h => h.1
  have hC : C = R ⊓ centralizer (L : Set G) := by
    dsimp only [C]
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    rw [← inf_assoc, inf_eq_left.mpr hRU]
  have hQ : Q = R ⊓ centralizer (L.conjBy x⁻¹ : Set G) := by
    change C.conjBy x⁻¹ = _
    rw [hC]
    change (R ⊓ centralizer (L : Set G)).map (MulAut.conj x⁻¹).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj x⁻¹).injective]
    change R.conjBy x⁻¹ ⊓ (centralizer (L : Set G)).conjBy x⁻¹ = _
    rw [hRx, cubic_map_centralizer]
  have hNQ : N ≤ normalizer (Q : Set G) := by
    rw [hQ]
    exact (le_inf inf_le_right
      (hNLx.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  obtain ⟨X, hXL, hXcard, hXSK, hXmove, hXfix⟩ :=
    MathieuSourceSetup.linear_four_cubic_torus_actor c hG hempty e
  have hXN : X ≤ N := by
    refine le_inf (le_inf (hXSK.trans (normalizer_le_normalizer_derived SK)) ?_) ?_
    · exact (hXL.trans (le_centralizer_iff.mp hDx)).trans
        (Subgroup.centralizer_le_normalizer _)
    · have hRgen : R = SK ⊔ C := by
        rw [hC]
        exact MathieuSourceSetup.ambient_thompson_product c hgen
          (MathieuSourceSetup.linear_four_thompson_product c hG localC129Input_knownSimple
            hempty hgen e)
      rw [hRgen]
      have hCL : C ≤ centralizer (L : Set G) := by rw [hC]; exact inf_le_right
      have hXNC : X ≤ normalizer (C : Set G) :=
        (hXL.trans (le_centralizer_iff.mp hCL)).trans (Subgroup.centralizer_le_normalizer _)
      exact (le_inf hXSK hXNC).trans (normalizer_inf_normalizer_le_normalizer_sup SK C)
  have hLXDC : L.conjBy x⁻¹ ≤ centralizer (D : Set G) := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) (le_centralizer_iff.mp hDx)
    change L.conjBy x⁻¹ ≤ (centralizer (D.conjBy x⁻¹ : Set G)).conjBy x⁻¹ at hh
    have he : D.conjBy ((x⁻¹) ^ 2) = D := mem_normalizer_iff_map_conj_eq.mp hxDinv
    rw [cubic_map_centralizer, conjBy_conjBy, ← pow_two, he] at hh
    exact hh
  have hXnot : ¬ X ≤ L.conjBy x⁻¹ := fun h => hXmove (h.trans hLXDC)
  let P₀ := P.mapSurjective
    (f := e.toMonoidHom.comp (QuotientGroup.mk' (center L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨Y, hXY, hYN, hYcard, _, _, y, hy, hpres⟩ :=
    CubicTerminal.exists_nine_common_sylow D R L X x hxD hxR hXcard hXL
      hXN hXnot hNLx α P₀ hαP hαker
  have hfix : SK ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G) := by
    rw [hXfix]
    rintro a ⟨b, hb, rfl⟩ k hk
    exact congrArg Subtype.val (mem_center_iff.mp hb ⟨k, hk⟩)
  have hQL : Q ≤ L := (MathieuSourceSetup.crossing_core_eq_cubic_commutator_le
    c hG hempty hgen e x hxT hxS hxN hx2 X hXcard hXL (hXN.trans hNQ) hfix).2
  have hQR : Q ≤ R := by rw [hQ]; exact inf_le_left
  have hQSK : Q ≤ SK := le_inf (hQR.trans hRU) hQL
  have hQne : ¬ IsElementaryAbelian 2 Q := by
    intro hQe
    let := hQe
    let eC : C ≃* Q := C.equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom
      (MulAut.conj x⁻¹).injective
    have hCe : IsElementaryAbelian 2 C :=
      IsElementaryAbelian.of_injective eC.toMonoidHom eC.injective
    let : Fact (IsPGroup 2 C) := ⟨(S.isPGroup'.map H.subtype).to_le
      (inf_le_left.trans hRU)⟩
    exact (MathieuSourceSetup.linear_four_crossing_preparation_knownSimple
      c hG hempty hgen e x hxT hxS hxN hx2).1
      ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mpr hCe)
  obtain ⟨f, hf, hk, β, hβker, hβact⟩ :=
    exists_equivariant_sylow_mark L N e P hNL α hα hαP hαker
  have hQeq : Q = (P : Subgroup L).map L.subtype :=
    MathieuSourceSetup.linear_four_nine_invariant_eq_sylow c hG hempty e P N f hk β
      hβker hβact Y Q hYN hYcard (hP.symm ▸ hQSK) (hYN.trans hNQ) hQne
  let W := X.conjBy y⁻¹
  have hWN : W ≤ N := by
    have hh := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hXY
    change W ≤ Y.conjBy y⁻¹ at hh
    have heY : Y.conjBy y⁻¹ = Y :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (Y : Set G)).inv_mem hy)
    rw [heY] at hh
    exact hh.trans hYN
  have hWcard : Nat.card W = 3 := by
    change Nat.card (X.map (MulAut.conj y⁻¹).toMonoidHom) = 3
    rw [card_map_of_injective (MulAut.conj y⁻¹).injective, hXcard]
  have hWC : W ≤ centralizer ((P : Subgroup L).map L.subtype : Set G) := by
    rw [← hQeq]
    apply (map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hXL).trans
    change L.conjBy y⁻¹ ≤ centralizer (Q : Set G)
    rw [hpres L hNLx]
    exact le_centralizer_iff.mp (by rw [hQ]; exact inf_le_right)
  exact cubic_not_centralize_equivariant_sylow L N P f hf β hβker hβact W hWcard hWN hWC

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
