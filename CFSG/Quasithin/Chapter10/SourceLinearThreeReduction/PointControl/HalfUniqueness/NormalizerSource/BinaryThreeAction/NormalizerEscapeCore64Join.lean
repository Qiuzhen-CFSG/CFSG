module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64Partner
public import Theory.ElementaryAbelian.Join

/-!
# The actual elementary join of the two full cores

The complete original abelian MS core and its exchanged copy are disjoint
and commute. Their literal join is the movement of O₂(L₀T) by L₀, and is
a normal elementary subgroup of order4096. The original selected module
is not substituted for either full core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 ChapterC.BinaryMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem relative_commutator_sup (R A B : Subgroup G)
    (ha : A ≤ normalizer (R : Set G)) (hb : B ≤ normalizer (R : Set G)) :
    ⁅R,A ⊔ B⁆ = ⁅R,A⁆ ⊔ ⁅R,B⁆ := by
  let W := ⁅R,A⁆ ⊔ ⁅R,B⁆
  have hWR : W ≤ R := sup_le (le_normalizer_iff_commutator_le_left.mp ha)
    (le_normalizer_iff_commutator_le_left.mp hb)
  have haW : A ≤ normalizer (W : Set G) := le_normalizer_iff_commutator_le_right.mpr
    ((commutator_mono le_rfl hWR).trans (by rw [commutator_comm]; exact le_sup_left))
  have hbW : B ≤ normalizer (W : Set G) := le_normalizer_iff_commutator_le_right.mpr
    ((commutator_mono le_rfl hWR).trans (by rw [commutator_comm]; exact le_sup_right))
  apply le_antisymm ?_ (sup_le (commutator_mono le_rfl le_sup_left)
    (commutator_mono le_rfl le_sup_right))
  rw [commutator_comm]
  exact commutator_sup_le_of_relative_normal (A ⊔ B) A B R W (sup_le haW hbW)
    le_sup_left le_sup_right (by rw [commutator_comm]; exact le_sup_left)
    (by rw [commutator_comm]; exact le_sup_right)

/-- The original orbit moves its actual join core onto a normal elementary
subgroup of rank twelve in the genuine abelian order64 branch. -/
theorem normalizerEscape_fullCore64_orbit_movement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))))
    (hcard : Nat.card ((commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64) :
    let U := ⁅(localJoin T L).pCoreIn 2,localOrbit T L⁆
    IsElementaryAbelian 2 U ∧ Nat.card U = 4096 ∧
      localJoin T L ≤ normalizer (U : Set G) := by
  let R := (localJoin T L).pCoreIn 2
  let C := ⁅R,L⁆
  let a := (MulAut.conj s.exchange).toMonoidHom
  let B := L.map a
  let Ct := C.map a
  obtain ⟨hC,hfixed,hB⟩ := normalizerEscape_fullCore64_partner_structure D s hout hc hcard
  let : IsElementaryAbelian 2 C := hC
  let : IsElementaryAbelian 2 Ct := IsElementaryAbelian.map a
  have hJR : localJoin T L ≤ normalizer (R : Set G) :=
    (localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have htR : R.map a = R := mem_normalizer_iff_map_conj_eq.mp
    (hJR ((show (T : Subgroup G) ≤ localJoin T L from le_sup_right) s.exchange_mem))
  have hCt : Ct = ⁅R,B⁆ := by change (⁅R,L⁆).map a = _; rw [map_commutator,htR]
  have hBJ : B ≤ localJoin T L :=
    ((orbit_eq_pair s).symm ▸ le_sup_right).trans le_sup_left
  have hCL : C ≤ L := by
    rw [show C = (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype from
      normalizerEscape_join_core_component D (selected_nonnormal s) hout s.quotient]
    let h := normalizerEscapeBinaryInput D (selected_nonnormal s) hout s.quotient
    exact (map_mono (h.commutatorCore_le.trans (map_subtype_le _))).trans_eq
      (map_subgroupOf_eq_of_le le_sup_left)
  have hCtB : Ct ≤ B := map_mono hCL
  have hback : B.map a = L := conjugate_twice_eq_of_index_two L T
    (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 (selected_nonnormal s))
    inf_le_right s.exchange_mem
  have hLCt : L ≤ centralizer (Ct : Set G) := by
    intro l hl x hx
    obtain ⟨b,hb,he⟩ := show l ∈ B.map a from hback.symm ▸ hl
    obtain ⟨c,hc,rfl⟩ := hx
    rw [←he]
    simpa only [map_mul] using congrArg a (hB hb c hc)
  have hdisj : Disjoint C Ct := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    exact hfixed.le ⟨hx.1,le_centralizer_iff.mp hLCt hx.2⟩
  have hcomm : Ct ≤ centralizer (C : Set G) := hCtB.trans hB
  let : IsElementaryAbelian 2 (C ⊔ Ct : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hcomm
  have hgen : ⁅R,localOrbit T L⁆ = C ⊔ Ct := by
    rw [orbit_eq_pair s,relative_commutator_sup R L B
      (((le_componentOrbit L T).trans le_sup_left).trans hJR) (hBJ.trans hJR),←hCt]
  have hCcard : Nat.card C = 64 := by
    change Nat.card (⁅(localJoin T L).pCoreIn 2,L⁆ : Subgroup G) = 64
    rwa [normalizerEscape_join_core_component D (selected_nonnormal s) hout s.quotient]
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C Ct hdisj
    (le_centralizer_iff.mp hcomm)
  have hsize : Nat.card (C ⊔ Ct : Subgroup G) = 4096 := by
    rw [←Nat.card_congr e.toEquiv,Nat.card_prod,show Nat.card Ct = Nat.card C from
      card_map_of_injective (MulAut.conj s.exchange).injective,hCcard]
  have hnormal : localJoin T L ≤ normalizer ((⁅R,localOrbit T L⁆ : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hgR : R.map (MulAut.conj g).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (hJR hg)
    have hgL : (localOrbit T L).map (MulAut.conj g).toMonoidHom = localOrbit T L :=
      mem_normalizer_iff_map_conj_eq.mp
        ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) hg)
    change (⁅R,localOrbit T L⁆).map (MulAut.conj g).toMonoidHom = _
    rw [map_commutator,hgR,hgL]
  change IsElementaryAbelian 2 (⁅R,localOrbit T L⁆ : Subgroup G) ∧ _ ∧ _
  rw [hgen] at hnormal ⊢
  exact ⟨inferInstance,hsize,hnormal⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
