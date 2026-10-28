module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearBetaCenters
public import Theory.Representation.BinaryConjugationSection.ComplementaryFixed

/-!
# Natural beta sections and the general field inequality

For two genuine linear endpoint markings, the original quotient Q_beta/Z_beta
carries the conjugation action of L_beta/Q_beta. The two elementary seeds
have complementary images and are fixed by their corresponding Sylow actors.
Their generation and quadratic action therefore give natural module copies.
The coordinate homomorphism remains the literal quotient projection.

The quotient order implies q_alpha=q_beta^r. Multiplicity one would make
all nonzero vectors conjugate to the image of an elementary seed. With the
central elementary kernel this makes Q_beta elementary, contradicting its
proved nonabelian structure. Hence r>=2 and q_beta^2<=q_alpha. No field
relation or center order is assumed, and only vertex stabilizers are finite.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.12)--(5.13), pp.113--115, and (11.6)(d), pp.172--174.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]
variable {k' : Type*} [Field k'] [Finite k'] [CharP k' 2]
local notation "F" => family P
local instance binaryAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K :=
  ZMod.algebra K 2

/-- The original beta-core quotient is a sum of natural beta modules. -/
theorem source_linear_linear_beta_natural_copies (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems F)
    {a b c : Vertex F} (hc : IsCriticalPair F a b)
    (hb : DGS85.b F = 1) (hcomm : ⁅Z F a,Z F b⁆ = ⊥)
    (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    ∃ hN : ((Z F b).subgroupOf (Q F b)).Normal, letI := hN
      ∃ hE : IsElementaryAbelian 2 (Q F b ⧸ (Z F b).subgroupOf (Q F b)), letI := hE
        let π := eb.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup b)))
        ∃ σ : Representation (ZMod 2) SL(2,k') (Additive (Q F b ⧸ (Z F b).subgroupOf (Q F b))),
          ∃ s : BinaryConjugationSection (d.localGroup b) (Q F b) (Z F b) (σ.comp π),
            (∀ x : Q F b, (s.coordinates x).toAdd =
              Additive.ofMul (QuotientGroup.mk' ((Z F b).subgroupOf (Q F b)) x)) ∧
            fixedSpace σ ⊤ = ⊥ ∧ SL2SylowFixedRecognition.NaturalCoordinates σ := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite (Q F b) := Finite.of_injective (inclusion (Q_le_stabilizer F b)) (inclusion_injective _)
  have hQL : Q F b ≤ L := (localGroup_core_eq F d b) ▸ map_subtype_le _
  have hZQ : Z F b ≤ Q F b := (source_Z_Q_U h b).1.trans (map_subtype_le _)
  have hnQ : L ≤ normalizer (Q F b : Set G) := (d.local_le b).trans (stabilizer_normalizes_Q F b)
  have hnZ : L ≤ normalizer (Z F b : Set G) := (d.local_le b).trans
    ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F b)).mp (Z_normal F b))
  let π := eb.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := eb.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = (Q F b).subgroupOf L := by
    have he : π.ker = pCore 2 L := by
      ext x
      change eb ((QuotientGroup.mk' (pCore 2 L)) x) = 1 ↔ _
      rw [←eb.map_one,eb.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    rw [he]
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hQL]
    exact localGroup_core_eq F d b
  obtain ⟨hN,_,hE⟩ := source_linear_linear_core_quotient h hB d hc hb hcomm hbc hac Ma ea Mb eb
  let := hN
  let := hE
  obtain ⟨σ,s,hs⟩ := exists_canonical L (Q F b) (Z F b) hQL hZQ hnQ hnZ π hπ hker
  refine ⟨hN,hE,σ,s,hs,?_⟩
  let A := Z F a ⊓ Q F b
  let C := Z F c ⊓ Q F b
  have hab := source_critical_one_adjacent hc hb
  have hpair : Q F b = A ⊔ C :=
    (source_linear_linear_beta_core_structure h hB d hc hb hcomm hbc hac Ma ea Mb eb).1
  have hinter : A ⊓ C = Z F b :=
    (source_linear_rankOne_center_intersections h hB d hc hb hcomm hbc hac Ma Mb ea).2.2.2
  have hZA : Z F b ≤ A := hinter ▸ inf_le_left
  have hZC : Z F b ≤ C := hinter ▸ inf_le_right
  have hgen : Q F b = (A ⊔ C) ⊔ Z F b := by rw [←hpair,sup_eq_left.mpr hZQ]
  have hinter : (A ⊔ Z F b) ⊓ (C ⊔ Z F b) = Z F b := by
    rwa [sup_eq_left.mpr hZA,sup_eq_left.mpr hZC]
  obtain ⟨g,hg,hga⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨c,hbc⟩
  let g₀ : L := ⟨g,hg⟩
  have hgb : g • b = b := d.local_le b hg
  have hconj : C = A.conjBy (g₀ : G) := by
    dsimp only [A,C,conjBy,g₀]
    rw [map_inf _ _ _ (MulAut.conj g).injective,←Z_translate,←Q_translate,hga,hgb]
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  have hesc : ¬ Z F a ≤ Q F b := fun hh => hc.2 (hh.trans (source_Z_Q_U h b).2)
  have hsupp := source_linear_center_supplement h hB d hab Mb eb hesc
  have hAL : Z F a ≤ L := le_sup_left.trans (hsupp.ge.trans (hT ▸ map_subtype_le _))
  have hQim : ((Q F b).subgroupOf L).map π = ⊥ := by rw [←hker,Subgroup.map_ker_self]
  have himage : ((Z F a).subgroupOf L).map π = (T.mapSurjective hπ : Subgroup SL(2,k')) := by
    have hh := congrArg (fun R : Subgroup G => (R.subgroupOf L).map π) hsupp
    rw [subgroupOf_sup hAL hQL,Subgroup.map_sup,hQim,sup_bot_eq,←hT] at hh
    have heT : ((T : Subgroup L).map L.subtype).subgroupOf L = T := by
      apply map_injective L.subtype_injective
      rw [map_subgroupOf_eq_of_le (map_subtype_le _)]
    rw [heT] at hh
    exact hh.symm
  have hfix : ⁅Z F a,A⁆ ≤ Z F b := by
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      ((le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative (Z F a))).trans
        (centralizer_le (show A ≤ Z F a from inf_le_left)))).le.trans bot_le
  have hfree := fixed_preimage_of_complementary_pair L (Q F b) (Z F b) A C (Z F a)
    σ π hπ s inf_le_right inf_le_right hgen hinter g₀ hconj (T.mapSurjective hπ) himage hfix
  have hglobal := section_fixed_bot_of_commutators L (Q F b) (Z F b) σ π s hfree
  have hgenerated := pair_section_generated L (Q F b) (Z F b) A C (Z F a)
    σ π s inf_le_right hgen g₀ hconj hfix
  rw [himage] at hgenerated
  have hquadcomm : ⁅⁅Q F b,Z F a⁆,Z F a⁆ ≤ Z F b := by
    have hdisp : ⁅Q F b,Z F a⁆ ≤ Z F a :=
      le_normalizer_iff_commutator_le_right.mp (source_adjacent_core_normalizes_center h hab)
    exact (commutator_mono hdisp le_rfl).trans
      ((commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative (Z F a)))).le.trans bot_le)
  have hquad := isQuadratic_of_triple_commutator_le L (Q F b) (Z F b) (Z F a) σ π s (by simpa only [commutator_comm] using hquadcomm)
  rw [himage] at hquad
  exact ⟨hglobal,sl2_natural_copies σ (T.mapSurjective hπ) hquad hgenerated hglobal⟩

/-- The alpha field is a power of the beta field with exponent at least two.
Multiplicity one would make the nonabelian beta core elementary. -/
theorem source_linear_linear_field_power (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems F)
    {a b c : Vertex F} (hc : IsCriticalPair F a b)
    (hb : DGS85.b F = 1) (hcomm : ⁅Z F a,Z F b⁆ = ⊥)
    (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    ∃ r : ℕ, 2 ≤ r ∧ Nat.card k = Nat.card k' ^ r := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h b
  let : Finite (Z F b) := Finite.of_injective (inclusion (Z_le_stabilizer F b)) (inclusion_injective _)
  let : Finite (Q F b) := Finite.of_injective (inclusion (Q_le_stabilizer F b)) (inclusion_injective _)
  obtain ⟨hN,hE,σ,s,_,_,r,e,he⟩ := source_linear_linear_beta_natural_copies
    h hB d hc hb hcomm hbc hac Ma ea Mb eb
  let := hN
  let := hE
  have hcard := (source_linear_linear_core_quotient h hB d hc hb hcomm hbc hac Ma ea Mb eb).choose_spec.1
  have hsize := Nat.card_congr e.toEquiv
  simp only [Nat.card_fun,Nat.card_fin] at hsize
  change Nat.card (Q F b ⧸ (Z F b).subgroupOf (Q F b)) = _ at hsize
  rw [hcard] at hsize
  have hpower : Nat.card k = Nat.card k' ^ r := by
    apply Nat.pow_left_injective (n := 2) (by decide)
    simpa only [←pow_mul,Nat.mul_comm] using hsize
  have hk : 1 < Nat.card k := by
    let := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hr0 : r ≠ 0 := by intro hr; rw [hr,pow_zero] at hpower; omega
  have hr1 : r ≠ 1 := by
    intro hr
    subst r
    let E := e.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 2 → k'))
    have hEact : ∀ g v, E (σ g v) = Matrix.mulVec g.val (E v) := fun g v => he g v 0
    let A := Z F a ⊓ Q F b
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ Z F a from inf_le_left)
    have hesc : ¬ A ≤ Z F b := by
      intro hle
      have hu := card_le_of_le hle
      have hs := (source_linear_linear_center_card_ratio h hB d hc hb hcomm hbc hac Ma ea Mb eb).1
      change Nat.card A = _ at hs
      rw [hs] at hu
      have hp : 0 < Nat.card (Z F b) := Nat.card_pos
      nlinarith
    let π := eb.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup b)))
    have hπ : Function.Surjective π := eb.surjective.comp (QuotientGroup.mk'_surjective _)
    let : IsElementaryAbelian 2 (Q F b) := elementary_core_of_natural_section
      (d.localGroup b) (Q F b) (Z F b) A σ π hπ s
      (le_centralizer_iff.mp (source_core_centralizes_center h b)) inf_le_right hesc E hEact
    exact (source_linear_linear_beta_core_structure h hB d hc hb hcomm hbc hac Ma ea Mb eb).2.2.2.1
      (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative (Q F b))))
  exact ⟨r,by omega,hpower⟩

/-- The general linear branch satisfies the genuine source field inequality. -/
theorem source_linear_linear_beta_square_le (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems F)
    {a b c : Vertex F} (hc : IsCriticalPair F a b)
    (hb : DGS85.b F = 1) (hcomm : ⁅Z F a,Z F b⁆ = ⊥)
    (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    Nat.card k' ^ 2 ≤ Nat.card k := by
  obtain ⟨r,hr,he⟩ := source_linear_linear_field_power h hB d hc hb hcomm hbc hac Ma ea Mb eb
  rw [he]
  exact Nat.pow_le_pow_right (Nat.card_pos (α := k')) hr

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
