module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.OrderTwelve
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SwappingTwelve
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.FactorCoordinates
public import Theory.GroupTheory.PCoreSurjective
import all CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.QuotientWreath
import all Theory.GroupTheory.QuaternionCentralProductTransport
/-!
# The marked wreath-centralizer quotient

For the original configuration of quasithin 13.9.8, the faithful square action
identifies the literal centralizer quotient with `S₃ × C₂`.  The second
coordinate records permutation of the two quaternion factors.  Consequently
the centralizer's 2-core has order 64 and moves a factor.  The native
three-overgroup geometry and weak closure then identify this core in the source.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} {m : PairData d}
namespace CoreData
variable (q : CoreData m)

/-- The relative factor has exactly the original ambient image. -/
theorem centralProductInC_left_image :
    q.centralProductInC.left.map
      (m.C.subtype.comp (q.Q.subgroupOf m.C).subtype) = q.factors.left.map q.Q.subtype := by
  change (q.factors.left.map (subgroupOfEquivOfLe q.le_C).symm.toMonoidHom).map _ = _
  rw [map_map]
  congr 1

/-- Preservation of the relative factor is the original ambient normalizer condition. -/
theorem relative_factor_normalizer [hn : (q.Q.subgroupOf m.C).Normal] (g : m.C) :
    q.centralProductInC.left.map (MulAut.conjNormal g).toMonoidHom = q.centralProductInC.left ↔
      (g : G) ∈ normalizer (q.factors.left.map q.Q.subtype : Set G) := by
  let j := m.C.subtype.comp (q.Q.subgroupOf m.C).subtype
  have hj : Function.Injective j := m.C.subtype_injective.comp (q.Q.subgroupOf m.C).subtype_injective
  have hc : j.comp (MulAut.conjNormal g).toMonoidHom =
      (MulAut.conj (g:G)).toMonoidHom.comp j := by
    ext x
    rfl
  rw [← (Subgroup.map_injective (f := j) hj).eq_iff, map_map,hc,← map_map,
    q.centralProductInC_left_image]
  exact mem_normalizer_iff_map_conj_eq.symm

theorem quotient_equiv_s3_c2 (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde))
    (hself : m.tilde d.T ⊓ centralizer (m.tilde q.Q : Set m.Tilde) ≤ m.tilde q.Q)
    (hgrowth : (d.T : Subgroup G) < m.C) (htz : ¬ IsConj m.t m.z)
    (a : G) (haQ : a ∈ q.Q) (haZ : a ∉ m.Z) (haz : IsConj a m.z)
    (hfactor : letI : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
      ∃ g : m.C, q.centralProductInC.left.map (MulAut.conjNormal g).toMonoidHom ≠
        q.centralProductInC.left) :
    letI : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
    ∃ e : (m.C ⧸ q.Q.subgroupOf m.C) ≃* (Equiv.Perm (Fin 3) × BinaryFourPlus.C2),
      ∀ g : m.C, (e (QuotientGroup.mk' (q.Q.subgroupOf m.C) g)).2 =
        (q.centralProductInC.quotientWreathAction (MulAut.conjNormal g)).right := by
  let : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
  obtain ⟨f,hf,hmark⟩ := q.exists_quotient_wreath_embedding h hE hfix hself
  let eH := MonoidHom.ofInjective hf
  have hH : Nat.card f.range = 12 := (Nat.card_congr eH.toEquiv).symm.trans
    (q.quotient_card_twelve_of_marked_nonfusion h hE hfix hself hgrowth htz a haQ haZ haz)
  obtain ⟨g,hg⟩ := hfactor
  let v := QuotientGroup.mk' (q.Q.subgroupOf m.C) g
  have hv : (eH v).val.right ≠ 1 := by
    change (f v).right ≠ 1
    rw [hmark]
    exact fun hh => hg ((q.centralProductInC.quotientWreathAction_right_eq_one_iff _).mp hh)
  obtain ⟨e,he⟩ := BinaryFourPlus.swapping_twelve_equiv f.range hH (eH v) hv
  refine ⟨eH.trans e,?_⟩
  intro x
  exact (he _).trans (congrArg RegularWreathProduct.right (hmark x))

theorem exists_twoCore_swapping (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde))
    (hself : m.tilde d.T ⊓ centralizer (m.tilde q.Q : Set m.Tilde) ≤ m.tilde q.Q)
    (hgrowth : (d.T : Subgroup G) < m.C) (htz : ¬ IsConj m.t m.z)
    (a : G) (haQ : a ∈ q.Q) (haZ : a ∉ m.Z) (haz : IsConj a m.z)
    (hfactor : letI : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
      ∃ g : m.C, q.centralProductInC.left.map (MulAut.conjNormal g).toMonoidHom ≠
        q.centralProductInC.left) :
    letI : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
    Nat.card (pCore 2 m.C) = 64 ∧ ∃ g : m.C, g ∈ pCore 2 m.C ∧
      q.centralProductInC.left.map (MulAut.conjNormal g).toMonoidHom ≠ q.centralProductInC.left := by
  let : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
  let N := q.Q.subgroupOf m.C
  let π := QuotientGroup.mk' N
  obtain ⟨f,hf,hmark⟩ := q.exists_quotient_wreath_embedding h hE hfix hself
  let eH := MonoidHom.ofInjective hf
  have hH : Nat.card f.range = 12 := (Nat.card_congr eH.toEquiv).symm.trans
    (q.quotient_card_twelve_of_marked_nonfusion h hE hfix hself hgrowth htz a haQ haZ haz)
  obtain ⟨g,hg⟩ := hfactor
  have hv : (eH (π g)).val.right ≠ 1 := by
    change (f (π g)).right ≠ 1
    rw [hmark]
    exact fun hh => hg ((q.centralProductInC.quotientWreathAction_right_eq_one_iff _).mp hh)
  obtain ⟨hc,hcross⟩ := BinaryFourPlus.swapping_twelve_twoCore f.range hH (eH (π g)) hv
  have hcore : Nat.card (pCore 2 (m.C ⧸ N)) = 2 := by
    have hh := congrArg (fun U : Subgroup f.range => Nat.card U) (pCore_map_iso 2 eH)
    rw [card_map_of_injective (f := eH.toMonoidHom) eH.injective,hc] at hh
    exact hh
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact q.isPGroup.comap_subtype
  have hNcard : Nat.card N = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe q.le_C).toEquiv).trans q.card
  constructor
  · rw [π.card_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective N) hker,
      QuotientGroup.ker_mk',hNcard,hcore]
  · have hn : Nontrivial (pCore 2 (m.C ⧸ N)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hcore]; decide)
    let := hn
    obtain ⟨y,hy⟩ := exists_ne (1 : pCore 2 (m.C ⧸ N))
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective N y.val
    have hxcore : x ∈ pCore 2 m.C := by
      rw [← π.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective N) hker]
      change π x ∈ pCore 2 (m.C ⧸ N)
      exact hx.symm ▸ y.property
    refine ⟨x,hxcore,?_⟩
    intro hxfix
    have hemem : eH y.val ∈ pCore 2 f.range := by
      rw [← pCore_map_iso 2 eH]
      exact mem_map_of_mem eH.toMonoidHom y.property
    have hene : eH y.val ≠ 1 := fun hh => hy
      (Subtype.ext (eH.injective (hh.trans eH.map_one.symm)))
    have hh := hcross (eH y.val) hemem hene
    apply hh
    change (f y.val).right = 1
    rw [← hx,hmark]
    exact (q.centralProductInC.quotientWreathAction_right_eq_one_iff _).mpr hxfix

theorem quotient_equiv_s3_c2_of_factor_moved (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde))
    (hself : m.tilde d.T ⊓ centralizer (m.tilde q.Q : Set m.Tilde) ≤ m.tilde q.Q)
    (hgrowth : (d.T : Subgroup G) < m.C) (htz : ¬ IsConj m.t m.z)
    (a : G) (haQ : a ∈ q.Q) (haZ : a ∉ m.Z) (haz : IsConj a m.z)
    (hfactor : ∃ g : G, g ∈ m.C ∧ g ∉ normalizer (q.factors.left.map q.Q.subtype : Set G)) :
    letI : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
    ∃ e : (m.C ⧸ q.Q.subgroupOf m.C) ≃* (Equiv.Perm (Fin 3) × BinaryFourPlus.C2),
      ∀ g : m.C, (e (QuotientGroup.mk' (q.Q.subgroupOf m.C) g)).2 =
        (q.centralProductInC.quotientWreathAction (MulAut.conjNormal g)).right := by
  let : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
  apply q.quotient_equiv_s3_c2 h hE hfix hself hgrowth htz a haQ haZ haz
  obtain ⟨g,hgC,hg⟩ := hfactor
  exact ⟨⟨g,hgC⟩,fun hh => hg ((q.relative_factor_normalizer ⟨g,hgC⟩).mp hh)⟩

theorem twoCore_not_le_factor_normalizer (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde))
    (hself : m.tilde d.T ⊓ centralizer (m.tilde q.Q : Set m.Tilde) ≤ m.tilde q.Q)
    (hgrowth : (d.T : Subgroup G) < m.C) (htz : ¬ IsConj m.t m.z)
    (a : G) (haQ : a ∈ q.Q) (haZ : a ∉ m.Z) (haz : IsConj a m.z)
    (hfactor : ∃ g : G, g ∈ m.C ∧ g ∉ normalizer (q.factors.left.map q.Q.subtype : Set G)) :
    Nat.card (m.C.pCoreIn 2) = 64 ∧
      ¬ m.C.pCoreIn 2 ≤ normalizer (q.factors.left.map q.Q.subtype : Set G) := by
  let : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
  have hf : ∃ g : m.C, q.centralProductInC.left.map (MulAut.conjNormal g).toMonoidHom ≠
      q.centralProductInC.left := by
    obtain ⟨g,hgC,hg⟩ := hfactor
    exact ⟨⟨g,hgC⟩,fun hh => hg ((q.relative_factor_normalizer ⟨g,hgC⟩).mp hh)⟩
  obtain ⟨hc,g,hg,hgn⟩ := q.exists_twoCore_swapping h hE hfix hself hgrowth htz a haQ haZ haz hf
  refine ⟨?_,?_⟩
  · exact (card_map_of_injective m.C.subtype_injective).trans hc
  · intro hle
    exact hgn ((q.relative_factor_normalizer g).mpr (hle (mem_map_of_mem m.C.subtype hg)))

end CoreData
end CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
