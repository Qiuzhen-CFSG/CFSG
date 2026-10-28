module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ActionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.GlobalSource
public import Stellmacher.ElementaryAbelianMaxOddPair
/-!
# The original conjugate torus acts on the selected block

An odd subgroup normalizing J(S) fixes each member of its two-member
maximum elementary family. Apply this to the selected Borel torus D and
conjugate the conclusion back to obtain Dˣ≤N_G(Q). The complete natural
2.4.6 source theorem then gives Dˣ≤N_G(L).

Inside M, the core normalizer preserves both M∩L and Q. Their product is
J(S)D by the original core and Thompson decompositions, so Dˣ also normalizes
J(S)D. The terminal existence theorem selects the literal original D and
establishes both conclusions for every x∈T−S, with no independent geometry.

Source: Aschbacher–Smith 2.4.8(4),(5), printed p.530, second paragraph.
The subsequent joint Hall torus construction remains separate.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem natural_coreNormalizer_normalizes_block
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hsingle : d.L0 = d.block)
    {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    normalizer (twoCore d.H : Set G) ≤ normalizer (d.block.map d.H.subtype : Set G) := by
  have h3 : ¬ ChapterC.IsAlternatingBlock d.block 3 := by
    intro ha
    obtain ⟨e⟩ := ha.equiv_alternatingFour
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    let : Group.IsSolvable d.block := Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
    exact hL.not_solvable
  have hn := d.coreNormalizer_normalizes_L0_source_of_not_three hG T hM hTM hunique h3
  rw [hsingle] at hn
  exact hn

theorem source_conjugate_torus_normalizes_block
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (D : Subgroup G) (hodd : Odd (Nat.card D))
    (hDR : D ≤ normalizer (Stellmacher.elementaryAbelianMaxJ
      ((d.S : Subgroup d.H).map d.H.subtype) : Set G))
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    D ≤ normalizer (twoCore d.H : Set G) ∧
      D.map (MulAut.conj x⁻¹).toMonoidHom ≤ normalizer (twoCore d.H : Set G) ∧
      D.map (MulAut.conj x⁻¹).toMonoidHom ≤ normalizer (d.block.map d.H.subtype : Set G) := by
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hg := d.single_natural_global_source hG T hST hsingle hK
  have hxi : x⁻¹ ∉ (d.S : Subgroup d.H).map d.H.subtype := by
    intro hh
    exact hxS (by simpa only [inv_inv] using ((d.S : Subgroup d.H).map d.H.subtype).inv_mem hh)
  have hpair := (hg.2.2.2.2 x⁻¹ (T.inv_mem hxT) hxi).2.1
  simp only [inv_inv] at hpair
  have hfix := Stellmacher.odd_normalizes_maximum_pair _ D _ _ hpair hDR hodd
  have hDxQ : D.map (MulAut.conj x⁻¹).toMonoidHom ≤ normalizer (twoCore d.H : Set G) := by
    have hm := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hfix.2).trans
      ((twoCore d.H).map (MulAut.conj x).toMonoidHom |>.le_normalizer_map (MulAut.conj x⁻¹).toMonoidHom)
    rw [Subgroup.map_map] at hm
    have he : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id G := by
      ext y
      simp [mul_assoc]
    simpa only [he,map_id] using hm
  have hn := natural_coreNormalizer_normalizes_block d hG T hsingle hL hM hTM hunique
  exact ⟨hfix.1,hDxQ,hDxQ.trans hn⟩

end CFSG.Quasithin.Chapter2.LinearShadows.Single

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem core_normalizer_in_M_normalizes_borel_product
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hn : normalizer (twoCore d.H : Set G) ≤ normalizer (d.block.map d.H.subtype : Set G))
    (D : Subgroup G) (hD : D ≤ M ⊓ d.block.map d.H.subtype)
    (hgen : ((d.S : Subgroup d.H).map d.H.subtype ⊓ d.block.map d.H.subtype) ⊔ D =
      M ⊓ d.block.map d.H.subtype) :
    M ⊓ normalizer (twoCore d.H : Set G) ≤ normalizer
      ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊔ D : Subgroup G) : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let C := S ⊓ centralizer (L : Set G)
  let B := M ⊓ L
  have hdec : R = (S ⊓ L) ⊔ C := (source_thompson_decomposition d hG T hST hsingle hL).1
  have hq := d.core_source hG T hST
  have hCQ : C ≤ twoCore d.H := by
    have he : twoCore d.H = d.U0.map d.H.subtype ⊔ C := by
      simpa only [hsingle,S,L,C] using hq.2.1
    exact le_sup_right.trans_eq he.symm
  have hQR : twoCore d.H ≤ R := le_sSup hq.2.2
  have hPB : S ⊓ L ≤ B := inf_le_inf d.full_pair.1.1.2.1 le_rfl
  have hRD : R ⊔ D = B ⊔ twoCore d.H := by
    apply le_antisymm
    · apply sup_le _ (hD.trans le_sup_left)
      rw [hdec]
      exact sup_le (hPB.trans le_sup_left) (hCQ.trans le_sup_right)
    · apply sup_le _ (hQR.trans le_sup_left)
      change ((S ⊓ L) ⊔ D) = B at hgen
      rw [←hgen]
      exact sup_le ((le_sup_left.trans_eq hdec.symm).trans le_sup_left) le_sup_right
  change M ⊓ normalizer (twoCore d.H : Set G) ≤ normalizer ((R ⊔ D : Subgroup G) : Set G)
  rw [hRD]
  have hB : M ⊓ normalizer (twoCore d.H : Set G) ≤ normalizer (B : Set G) :=
    (le_inf (inf_le_left.trans M.le_normalizer) (inf_le_right.trans hn)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf hB inf_le_right).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem source_conjugate_torus_normalizes_borel_product
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (D : Subgroup G) (hD : D ≤ M ⊓ d.block.map d.H.subtype)
    (hodd : Odd (Nat.card D))
    (hDR : D ≤ normalizer (Stellmacher.elementaryAbelianMaxJ
      ((d.S : Subgroup d.H).map d.H.subtype) : Set G))
    (hgen : ((d.S : Subgroup d.H).map d.H.subtype ⊓ d.block.map d.H.subtype) ⊔ D =
      M ⊓ d.block.map d.H.subtype)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    D.map (MulAut.conj x⁻¹).toMonoidHom ≤ normalizer
      ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊔ D : Subgroup G) : Set G) := by
  have hnorm := source_conjugate_torus_normalizes_block d hG T hST hsingle hL
    hM hTM hunique D hodd hDR x hxT hxS
  have hn := natural_coreNormalizer_normalizes_block d hG T hsingle hL hM hTM hunique
  have hDxM : D.map (MulAut.conj x⁻¹).toMonoidHom ≤ M := by
    rintro _ ⟨y,hy,rfl⟩
    change x⁻¹ * y * (x⁻¹)⁻¹ ∈ M
    rw [inv_inv]
    exact M.mul_mem (M.mul_mem (M.inv_mem (hTM hxT)) (hD hy).1) (hTM hxT)
  exact (le_inf hDxM hnorm.2.1).trans
    (core_normalizer_in_M_normalizes_borel_product d hG T hST hsingle hL hn D hD hgen)

end CFSG.Quasithin.Chapter2.LinearShadows.Single

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original ambient torus, with both conjugate normalization conclusions
constructed for every x in T−S. -/
theorem source_ambient_borel_conjugate_torus
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    ∃ D : Subgroup G, D ≤ M ⊓ L ∧ Odd (Nat.card D) ∧ IsCyclic D ∧
      Nat.card D = 2^n - 1 ∧ D ≠ ⊥ ∧ (S ⊓ L) ⊔ D = M ⊓ L ∧
      D ≤ normalizer (R : Set G) ∧ S ≤ normalizer ((R ⊔ D : Subgroup G) : Set G) ∧
      ∀ x ∈ T, x ∉ S →
        D.map (MulAut.conj x⁻¹).toMonoidHom ≤ normalizer (L : Set G) ∧
        D.map (MulAut.conj x⁻¹).toMonoidHom ≤ normalizer ((R ⊔ D : Subgroup G) : Set G) := by
  obtain ⟨P,D,hP,_hB,hDB,hodd,_hd,hgen,_hHall,hcyc,hcard,hne,hDR,hSRD⟩ :=
    source_borel_torus_action d hG T hST hsingle hL
  let f := d.H.subtype.comp d.block.subtype
  let D₀ := D.map f
  have hf : Function.Injective f := d.H.subtype_injective.comp d.block.subtype_injective
  have hD₀ : D₀ ≤ M ⊓ d.block.map d.H.subtype := by
    rintro _ ⟨y,hy,rfl⟩
    exact ⟨hDB hy,mem_map_of_mem d.H.subtype y.property⟩
  have hodd₀ : Odd (Nat.card D₀) := by rwa [card_map_of_injective hf]
  have hcard₀ : Nat.card D₀ = 2^n - 1 := by rwa [card_map_of_injective hf]
  have hne₀ : D₀ ≠ ⊥ := fun he => hne ((map_eq_bot_iff_of_injective D hf).mp he)
  have hcyc₀ : IsCyclic D₀ := by
    let := hcyc
    let e := equivMapOfInjective D f hf
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hgen₀ : ((d.S : Subgroup d.H).map d.H.subtype ⊓ d.block.map d.H.subtype) ⊔ D₀ =
      M ⊓ d.block.map d.H.subtype := by
    have he := congrArg (Subgroup.map f) hgen
    have hPi : (P : Subgroup d.block).map f =
        (d.S : Subgroup d.H).map d.H.subtype ⊓ d.block.map d.H.subtype := by
      dsimp only [f]
      rw [←map_map,hP,map_inf _ _ _ d.H.subtype_injective]
    have hBi : ((M.subgroupOf d.H).subgroupOf d.block).map f = M ⊓ d.block.map d.H.subtype := by
      change (M.comap f).map f = _
      rw [map_comap_eq,MonoidHom.range_comp,range_subtype,inf_comm]
    rwa [Subgroup.map_sup,hPi,hBi] at he
  refine ⟨D₀,hD₀,hodd₀,hcyc₀,hcard₀,hne₀,hgen₀,hDR,hSRD,?_⟩
  intro x hxT hxS
  exact ⟨(source_conjugate_torus_normalizes_block d hG T hST hsingle hL hM hTM
    hunique D₀ hodd₀ hDR x hxT hxS).2.2,
    source_conjugate_torus_normalizes_borel_product d hG T hST hsingle hL hM hTM hunique
      D₀ hD₀ hodd₀ hDR hgen₀ x hxT hxS⟩

end CFSG.Quasithin.Chapter2.LinearShadows.Single
