module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointNormalitySource
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointMembership
public import Theory.GroupTheory.PrimeRankCentralCover
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedCenter

/-!
# Quasisimple marks of the original tensor point component

The nonsingular point is an actual central involution of every containing
component inside its centralizer. Its full module has at most four fixed
vectors, and at most two when the containing center has order at most two.
Thus the induced automorphisms have two-rank at least six, or seven in the
latter case. Faithful descent for perfect groups gives the same lower bounds
on automorphisms of the literal central quotient. SQTK inheritance supplies
the complete source Theorem C catalogue on that quotient.

Source: Aschbacher--Smith 9.4.1, printed p.735. These are source marks;
the individual catalogue exclusions are proved in the importing consumers.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- A center of order at most two bounds the actual full-module action kernel. -/
theorem tensorPoint_containing_automorphism_rank_seven (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (hZ : Nat.card (center I) ≤ 2) :
    7 ≤ primeRank 2 (MulAut I) := by
  let : IsElementaryAbelian 2 D.fullModule := m.fullModule_elementary
  have hVV : D.fullModule ≤ centralizer (D.fullModule : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hVX : D.fullModule ≤ centralizer ({(v : G)} : Set G) :=
    hVV.trans (centralizer_le (Set.singleton_subset_iff.mpr v.property))
  let f : D.fullModule →* MulAut I :=
    I.normalizerMonoidHom.comp (inclusion (hVX.trans hIN))
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hk : f.ker = (D.fullModule ⊓ centralizer (I : Set G)).subgroupOf D.fullModule := by
    ext x
    constructor
    · intro hx
      have hx' : inclusion (hVX.trans hIN) x ∈ I.normalizerMonoidHom.ker := hx
      rw [normalizerMonoidHom_ker] at hx'
      exact ⟨x.property,hx'⟩
    · intro hx
      change inclusion (hVX.trans hIN) x ∈ I.normalizerMonoidHom.ker
      rw [normalizerMonoidHom_ker]
      exact hx.2
  have hker : Nat.card f.ker ≤ 2 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe (show
      D.fullModule ⊓ centralizer (I : Set G) ≤ D.fullModule from inf_le_left)).toEquiv]
    have hle := card_le_of_le (m.tensorPoint_containing_fixed_le_center v hv hLI)
    exact hle.trans ((Nat.le_of_dvd (Nat.card_pos (α := center I))
      (card_map_dvd (center I) I.subtype)).trans hZ)
  by_contra hn
  have hr : primeRank 2 (MulAut I) ≤ 6 := by omega
  have hsmall : Nat.card f.range ≤ 64 :=
    (primeRank_le_iff_elementary_card_le (MulAut I)).mp hr f.range inferInstance
  have htotal := f.ker.index_mul_card
  rw [index_ker,m.card_fullModule] at htotal
  have hbound := Nat.mul_le_mul hsmall hker
  rw [htotal] at hbound
  omega

/-- Every subgroup of this involution centralizer inherits the full SQTK condition. -/
theorem tensorPoint_containing_sqtk (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hIX : I ≤ centralizer ({(v : G)} : Set G)) :
    IsSQTK KnownSimple.IsKnownSimple I := by
  let : IsElementaryAbelian 2 D.fullModule := m.fullModule_elementary
  have hv2 : orderOf (v : G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (v : G) v.property)
      (m.tensorPoint_ne_one v hv)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hIX)).mp
    ((D.simpleQTKE.involution_centralizer_sqtk hv2).subgroup (I.subgroupOf _))

/-- The actual quasisimple central quotient belongs to the full source C catalogue. -/
theorem tensorPoint_containing_quotient_theoremC (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hIX : I ≤ centralizer ({(v : G)} : Set G))
    [IsQuasisimple I] :
    ChapterA.Section02.IsTheoremCModel (I ⧸ center I) :=
  ChapterA.Section03.SourceEmbeddings.quasisimple_center_quotient_theoremC_model
    (m.tensorPoint_containing_sqtk v hv hIX)



/-- The original nonsingular point supplies an involution in the actual center. -/
theorem tensorPoint_containing_two_dvd_center (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G)) :
    2 ∣ Nat.card (center I) := by
  let : IsElementaryAbelian 2 D.fullModule := m.fullModule_elementary
  have hv2 : orderOf (v : G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (v : G) v.property)
      (m.tensorPoint_ne_one v hv)
  have hd := ((center I).map I.subtype).orderOf_dvd_natCard
    (m.tensorPoint_mem_center_of_containing v hv hLI hIX)
  rw [hv2, card_map_of_injective I.subtype_injective] at hd
  exact hd

/-- The original rank-six action descends faithfully through the whole center. -/
theorem tensorPoint_containing_quotient_automorphism_rank (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [Group.IsPerfect I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    6 ≤ primeRank 2 (MulAut (I ⧸ center I)) :=
  (m.tensorPoint_containing_automorphism_rank v hv hLI hIN).trans
    (automorphism_primeRank_le_quotient_center (E := I) 2)

/-- The rank-seven refinement also descends through the literal central quotient. -/
theorem tensorPoint_containing_quotient_automorphism_rank_seven (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [Group.IsPerfect I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (hZ : Nat.card (center I) ≤ 2) :
    7 ≤ primeRank 2 (MulAut (I ⧸ center I)) :=
  (m.tensorPoint_containing_automorphism_rank_seven v hv hLI hIN hZ).trans
    (automorphism_primeRank_le_quotient_center (E := I) 2)

/-- The containing component cannot have trivial center. -/
theorem tensorPoint_containing_center_ne_bot (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G)) : center I ≠ ⊥ := by
  intro hZ
  have hd := m.tensorPoint_containing_two_dvd_center v hv hLI hIX
  simp only [hZ, Nat.card_eq_fintype_card] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
