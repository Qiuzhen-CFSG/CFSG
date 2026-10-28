module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSDoubledMarking
public import Theory.Representation.SL3DoubledNaturalOffenders.LargeElementary
public import Theory.Representation.SL3DoubledNaturalOffenders.ParabolicDisplacement
public import Theory.SpecificGroups.SL3.ParabolicFixer

/-!
# Excluding the original doubled row and selecting the third MS row

The actual self-centralizing core Q carries two natural SL₃ modules.
Every elementary subgroup of KS of order at least |Q| induces an offender
on Q, and the full binary normalizer estimate places it inside K. This
applies to the original conjugate Qᵗ, with both subtype maps retained.
The simultaneous original line and Sylow markings also place its nonzero
quotient image in the actual line radical.

Both Q and Qᵗ are L-invariant, since t normalizes L. Their intersection
contains the displacements of Qᵗ on each natural copy, so the additive
line-plane calculation gives [Q,L]≤Qᵗ. Conjugating and using t²∈S gives
[Qᵗ,L]≤Q. The line-local automorphism fixer then puts [Qᵗ,K] inside Q,
contradicting the original crossing obstruction. No identity W=[Q,L]
is assumed. This proves the doubled-row exclusion and constructs marked
third-row MSData from the exact earlier whole-core alternatives, with an
application to the original secondary component and quadratic root orbit.

Full quotient recognition and whole-core classification retain their existing
producer, qt-c134-nonbinary-linear-three-source. Strict secondary-core
enlargement and the final nonblock contradiction remain separate obligations.
No universal MS interface is used.
Source: Aschbacher--Smith C.1.36(2), printed p.140; C.4.7, p.153;
original 4.3.10 and 4.3.11--14, pp.616--618.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledMarking
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

omit [Finite G] in
private theorem whole_coordinates {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) :
    ∃ f : Q c ≃* Multiplicative (Fin 2 → Fin 3 → F),
      ∀ (k : K c) (u v : Q c), (v : G) = k * (u : G) * (k : G)⁻¹ →
        (f v).toAdd = Representation.SL3DoubledNaturalOffenders.representation F
          (linearThreeActor e k) (f u).toAdd := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,_,a,ha⟩ := hm
  let b := QuotientGroup.quotientBot.symm.trans a
  let t := (LinearEquiv.finTwoArrow (ZMod 2) (Fin 3 → F)).symm
  refine ⟨b.trans t.toAddEquiv.toMultiplicative,?_⟩
  intro k u v huv
  apply t.symm.injective
  change (b v).toAdd = _
  exact ha k u v huv

omit [Finite G] in
private theorem whole_elementary {F : Type*} [Field F] [CharP F 2]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) :
    IsElementaryAbelian 2 (Q c) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨f,_⟩ := whole_coordinates e hm
  let : IsElementaryAbelian 2 (Multiplicative (Fin 2 → Fin 3 → F)) := by
    refine { toIsMulCommutative := ⟨⟨fun x y => mul_comm x y⟩⟩
             exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro x
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    change x.toAdd + x.toAdd = 0
    calc
      _ = (2 : F) • x.toAdd := (two_smul F x.toAdd).symm
      _ = 0 := by rw [show (2 : F) = 0 from CharTwo.two_eq_zero,zero_smul]
  exact IsElementaryAbelian.of_injective f.toMonoidHom f.injective

/-- The containment clause of C.1.36(2) on the original KS. Every
large elementary subgroup is in the actual embedded component K. -/
theorem large_elementary_le_component_of_doubled {F : Type} [Field F] [Finite F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAJ : A ≤ K c ⊔ S c)
    (hcard : Nat.card (Q c) ≤ Nat.card A) : A ≤ K c := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let J := K c ⊔ S c
  let Qi := (Q c).subgroupOf J
  let Ki := (K c).subgroupOf J
  have hJK : J ≤ normalizer (K c : Set G) :=
    sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le)
  have hJH : J ≤ c.H := sup_le (map_subtype_le _) inf_le_right
  let : Qi.Normal := normal_subgroupOf_of_le_normalizer (hJH.trans (core_normalized c))
  let : Ki.Normal := normal_subgroupOf_of_le_normalizer hJK
  let : IsElementaryAbelian 2 (Q c) := whole_elementary e hm
  let : IsElementaryAbelian 2 Qi := IsElementaryAbelian.comap_of_injective
    J.subtype J.subtype_injective (Q c)
  let : IsElementaryAbelian 2 (A.subgroupOf J) := IsElementaryAbelian.comap_of_injective
    J.subtype J.subtype_injective A
  have hQK : Q c ≤ K c := (component_core_eq_of_doubled D hf n hn hF e hm).symm ▸ pCoreIn_le 2 (K c)
  have hQJ : Q c ≤ J := hQK.trans le_sup_left
  have hC : centralizer (Qi : Set J) = Qi := by
    have hc := join_core_centralizer_of_doubled D hf n hn hF e hm
    ext x
    constructor
    · intro hx
      apply hc.le
      refine ⟨x.property,?_⟩
      intro q hq
      exact congrArg (fun z : J => (z : G)) (hx ⟨q,hQJ hq⟩ hq)
    · intro hx y hy
      exact Subtype.ext (congrArg (fun z : Q c => (z : G))
        (mul_comm (⟨y,hy⟩ : Q c) ⟨x,hx⟩))
  let a : Ki ≃* K c := subgroupOfEquivOfLe (show K c ≤ J from le_sup_left)
  let b : Qi ≃* Q c := subgroupOfEquivOfLe hQJ
  obtain ⟨f,hf'⟩ := whole_coordinates e hm
  have hle := Representation.SL3DoubledNaturalOffenders.large_elementary_le_component
    Qi Ki (fun _ hx => hQK hx) hC hn hF
    ((linearThreeActor e).comp a.toMonoidHom)
    ((e.surjective.comp (QuotientGroup.mk'_surjective _)).comp a.surjective)
    (b.trans f) (fun k u v huv => hf' (a k) (b u) (b v) (congrArg (fun z : J => (z : G)) huv))
    (A.subgroupOf J) (by
      rw [Nat.card_congr b.toEquiv,Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv]
      exact hcard)
  intro x hx
  exact hle (show (⟨x,hAJ hx⟩ : J) ∈ A.subgroupOf J from hx)

/-- The actual crossed Q is elementary, of the same order, and contained
in K in the doubled row. No equality of W with [Q,L] is used. -/
theorem crossing_core_le_component_of_doubled {F : Type} [Field F] [Finite F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) :
    (Q c).map (MulAut.conj c.t⁻¹).toMonoidHom ≤ K c := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let : IsElementaryAbelian 2 (Q c) := whole_elementary e hm
  let : IsElementaryAbelian 2 ((Q c).map (MulAut.conj c.t⁻¹).toMonoidHom) :=
    IsElementaryAbelian.map _
  apply large_elementary_le_component_of_doubled D hf n hn hF e hm
  · have hs : (S c).map (MulAut.conj c.t⁻¹).toMonoidHom = S c :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (S c : Set G)).inv_mem c.crossing_normalizes)
    exact ((map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom) (core_le_sylow c)).trans_eq hs).trans le_sup_right
  · rw [card_map_of_injective (MulAut.conj c.t⁻¹).injective]

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledMarking

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledMarking
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

omit [Finite G] in
private theorem crossed_normalized_local
    (D : Chapter12.Section02.ChosenModule T L V) :
    L ≤ normalizer ((Q c).map (MulAut.conj c.t⁻¹).toMonoidHom : Set G) := by
  have hL : L.map (MulAut.conj c.t⁻¹).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp
      (D.sylow_normalizes_component ((T : Subgroup G).inv_mem c.crossing_mem))
  have hnorm : L ≤ normalizer (Q c : Set G) :=
    (c.le_component.trans (map_subtype_le _)).trans (core_normalized c)
  have hm := (map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom) hnorm).trans
    ((Q c).le_normalizer_map (MulAut.conj c.t⁻¹).toMonoidHom)
  rwa [hL] at hm

/-- Under the simultaneous original markings, the crossed core has a
nontrivial image in the actual line radical, normalized by the full line
local. This keeps the full SL₃ quotient and its original Sylow placement. -/
theorem crossing_image_nontrivial_le_lineCore {F : Type} [Field F] [Finite F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)))
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F)
    (hS : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor e) = unipotentSL F) :
    let A := (Q c).map (MulAut.conj c.t⁻¹).toMonoidHom
    let B := (A.subgroupOf (K c)).map (linearThreeActor e)
    B ≠ ⊥ ∧ B ≤ (lineLocalSL F).pCoreIn 2 ∧
      lineLocalSL F ≤ normalizer (B : Set SL(3,F)) := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let A := (Q c).map (MulAut.conj c.t⁻¹).toMonoidHom
  let B := (A.subgroupOf (K c)).map (linearThreeActor e)
  change B ≠ ⊥ ∧ B ≤ (lineLocalSL F).pCoreIn 2 ∧ _
  have hAK : A ≤ K c := crossing_core_le_component_of_doubled D hf n hn hF e hm
  have hAS : A ≤ S c := by
    have hs : (S c).map (MulAut.conj c.t⁻¹).toMonoidHom = S c :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (S c : Set G)).inv_mem c.crossing_normalizes)
    exact (map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom) (core_le_sylow c)).trans_eq hs
  have hBp : IsPGroup 2 B := ((T.isPGroup'.to_le (hAS.trans inf_le_left)).comap_subtype).map (linearThreeActor e)
  have hBS : B ≤ unipotentSL F := by
    let P := ((S c).subgroupOf (K c)).map (linearThreeActor e)
    have hp : IsPGroup 2 P := ((T.isPGroup'.to_le inf_le_left).comap_subtype).map (linearThreeActor e)
    have hUP : unipotentSL F ≤ P := hS ▸ map_mono (comap_mono (show S c ⊓ L ≤ S c from inf_le_left))
    have heq : P = unipotentSL F :=
      (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F (by omega : 0<n) hF).is_maximal' hp hUP
    exact (map_mono (comap_mono hAS)).trans_eq heq
  have hLB : lineLocalSL F ≤ normalizer (B : Set SL(3,F)) := by
    have hnL : L.subgroupOf (K c) ≤ normalizer (A.subgroupOf (K c) : Set (K c)) := by
      rw [←subgroupOf_normalizer_eq hAK]
      exact comap_mono (crossed_normalized_local D)
    rw [←hL]
    exact (map_mono hnL).trans ((A.subgroupOf (K c)).le_normalizer_map (linearThreeActor e))
  have hne : B ≠ ⊥ := by
    intro hb
    have hAQ : A ≤ Q c := by
      intro a ha
      have hh := mem_map_of_mem (linearThreeActor e) (show (⟨a,hAK ha⟩ : K c) ∈ A.subgroupOf (K c) from ha)
      rw [show (A.subgroupOf (K c)).map (linearThreeActor e) = ⊥ from hb] at hh
      have hk : (⟨a,hAK ha⟩ : K c) ∈ pCore 2 (K c) :=
        (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp (show linearThreeActor e ⟨a,hAK ha⟩ = 1 from hh))
      rw [←component_core_eq_of_doubled D hf n hn hF e hm]
      exact mem_map_of_mem (K c).subtype hk
    apply crossing_core_commutator_not_le c hf
    exact (commutator_mono le_rfl hAQ).trans (le_normalizer_iff_commutator_le_right.mp
      ((map_subtype_le _).trans (core_normalized c)))
  exact ⟨hne,le_pCoreIn_of_normalizes hBp (hBS.trans inf_le_right) hLB,hLB⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledMarking

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledMarking
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

private theorem local_commutator_le_crossed {F : Type} [Field F] [Finite F]
    [Algebra (ZMod 2) F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)))
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    ⁅Q c,L⁆ ≤ (Q c).map (MulAut.conj c.t⁻¹).toMonoidHom := by
  classical
  let A := (Q c).map (MulAut.conj c.t⁻¹).toMonoidHom
  have hAK : A ≤ K c := crossing_core_le_component_of_doubled D hf n hn hF e hm
  have hLQ : L ≤ normalizer (Q c : Set G) :=
    (c.le_component.trans (map_subtype_le _)).trans (core_normalized c)
  have hLA : L ≤ normalizer (A : Set G) := crossed_normalized_local D
  have hQA : Q c ≤ normalizer (A : Set G) := by
    have hs : (S c).map (MulAut.conj c.t⁻¹).toMonoidHom = S c :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (S c : Set G)).inv_mem c.crossing_normalizes)
    have ht := (map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom)
      (inf_le_right.trans (core_normalized c) : S c ≤ normalizer (Q c : Set G))).trans
        ((Q c).le_normalizer_map (MulAut.conj c.t⁻¹).toMonoidHom)
    rw [hs] at ht
    exact (core_le_sylow c).trans ht
  have hAQ : ¬ A ≤ Q c := by
    intro hh
    apply crossing_core_commutator_not_le c hf
    exact (commutator_mono le_rfl hh).trans
      (le_normalizer_iff_commutator_le_right.mp
        ((map_subtype_le _).trans (core_normalized c)))
  obtain ⟨a,ha,haQ⟩ := SetLike.not_le_iff_exists.mp hAQ
  let k : K c := ⟨a,hAK ha⟩
  have hk : linearThreeActor e k ≠ 1 := by
    intro hz
    have hp := (QuotientGroup.eq_one_iff k).mp (e.map_eq_one_iff.mp hz)
    apply haQ
    rw [←component_core_eq_of_doubled D hf n hn hF e hm]
    exact mem_map_of_mem (K c).subtype hp
  obtain ⟨f,he⟩ := whole_coordinates e hm
  let C : AddSubgroup (Fin 2 → Fin 3 → F) :=
    (((Q c ⊓ A).subgroupOf (Q c)).map f.toMonoidHom).toAddSubgroup'
  have hC (u : Q c) : (f u).toAdd ∈ C ↔ (u : G) ∈ A := by
    change f u ∈ ((Q c ⊓ A).subgroupOf (Q c)).map f.toMonoidHom ↔ _
    constructor
    · rintro ⟨v,hv,hvu⟩
      have hvu : v = u := f.injective hvu
      change (v : G) ∈ Q c ∧ (v : G) ∈ A at hv
      exact (congrArg (fun w : Q c => (w : G)) hvu) ▸ hv.2
    · intro hu
      exact mem_map_of_mem f.toMonoidHom (show u ∈ (Q c ⊓ A).subgroupOf (Q c) from ⟨u.property,hu⟩)
  have hconj (l : L) (u : Q c) :
      ∃ v : Q c, (v : G) = (l : G) * u * (l : G)⁻¹ ∧
        (f v).toAdd = Representation.SL3DoubledNaturalOffenders.representation F
          (linearThreeActor e ⟨l,c.le_component l.property⟩) (f u).toAdd := by
    let v := (Q c).normalizerMonoidHom ⟨l,hLQ l.property⟩ u
    have hv : (v : G) = l * (u : G) * (l : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    exact ⟨v,hv,he ⟨l,c.le_component l.property⟩ u v hv⟩
  have hCinv : ∀ g ∈ lineLocalSL F, ∀ v ∈ C,
      Representation.SL3DoubledNaturalOffenders.representation F g v ∈ C := by
    intro g hg v hv
    obtain ⟨l,hl,rfl⟩ := hL.ge hg
    let u := f.symm (Multiplicative.ofAdd v)
    have hu : (u : G) ∈ A := (hC u).mp (by simpa only [u,f.apply_symm_apply,toAdd_ofAdd] using hv)
    obtain ⟨w,hw,heq⟩ := hconj ⟨l,hl⟩ u
    have hwA : (w : G) ∈ A := by
      rw [hw]
      exact (mem_normalizer_iff.mp (hLA hl) _).mp hu
    have hmem := (hC w).mpr hwA
    rw [heq] at hmem
    simpa only [u,f.apply_symm_apply,toAdd_ofAdd] using hmem
  have hmove : ∀ v, Representation.SL3DoubledNaturalOffenders.representation F
      (linearThreeActor e k) v - v ∈ C := by
    intro v
    let u := f.symm (Multiplicative.ofAdd v)
    let w := (Q c).normalizerMonoidHom ⟨a,(hAK.trans
      ((map_subtype_le _).trans (core_normalized c))) ha⟩ u
    have hw : (w : G) = a * (u : G) * a⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    have hcomm : ((w*u⁻¹ : Q c) : G) ∈ A := by
      change (w : G) * (u : G)⁻¹ ∈ A
      rw [hw]
      exact (le_normalizer_iff_commutator_le_left.mp hQA)
        (commutator_mem_commutator ha u.property)
    have hmem := (hC (w*u⁻¹)).mpr hcomm
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,he k u w hw] at hmem
    simpa only [u,f.apply_symm_apply,toAdd_ofAdd,sub_eq_add_neg] using hmem
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl q hq
  let u : Q c := ⟨q,hq⟩
  obtain ⟨w,hw,heq⟩ := hconj ⟨l,hl⟩ u
  have hd := Representation.SL3DoubledNaturalOffenders.line_displacement_mem_of_nontrivial_actor
    C hCinv (linearThreeActor e k) hk hmove (linearThreeActor e ⟨l,c.le_component hl⟩)
      (hL.le (mem_map_of_mem _ hl)) (f u).toAdd
  have hmem : ((w*u⁻¹ : Q c) : G) ∈ A := by
    apply (hC (w*u⁻¹)).mp
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,heq]
    simpa only [sub_eq_add_neg] using hd
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,hw,commutatorElement_def] using hmem

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledMarking

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledMarking
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

private theorem false_of_marked_doubled {F : Type} [Field F] [Finite F]
    [CharP F 2] [Algebra (ZMod 2) F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)))
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) : False := by
  let t := (MulAut.conj c.t⁻¹).toMonoidHom
  let A := (Q c).map t
  have hAK : A ≤ K c := crossing_core_le_component_of_doubled D hf n hn hF e hm
  have htL : L.map t = L := mem_normalizer_iff_map_conj_eq.mp
    (D.sylow_normalizes_component ((T : Subgroup G).inv_mem c.crossing_mem))
  have htA : A.map t = Q c := by
    rw [map_map]
    have hcomp : t.comp t = (MulAut.conj ((c.t^2)⁻¹)).toMonoidHom := by
      ext x
      simp only [t,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,pow_two,mul_inv_rev,inv_inv]
      group
    rw [hcomp]
    exact mem_normalizer_iff_map_conj_eq.mp ((normalizer (Q c : Set G)).inv_mem
      (core_normalized c c.crossing_square.2))
  have hlocal : ⁅A,L⁆ ≤ Q c := by
    have hh := map_mono (f := t) (local_commutator_le_crossed D hf n hn hF e hm hL)
    rwa [map_commutator,htL,htA] at hh
  have hcore := component_core_eq_of_doubled D hf n hn hF e hm
  let f := linearThreeActor e
  have hzero (x : K c) (hx : (x : G) ∈ Q c) : f x = 1 := by
    have hi : x ∈ pCore 2 (K c) := by
      apply (mem_map_iff_mem (K c).subtype_injective).mp
      change (x : G) ∈ (K c).pCoreIn 2
      rwa [hcore]
    exact e.map_eq_one_iff.mpr ((QuotientGroup.eq_one_iff x).mpr hi)
  have hback (x : K c) (hx : f x = 1) : (x : G) ∈ Q c := by
    rw [←hcore]
    exact mem_map_of_mem (K c).subtype ((QuotientGroup.eq_one_iff x).mp (e.map_eq_one_iff.mp hx))
  apply crossing_core_commutator_not_le c hf
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha k hk
  let u : K c := ⟨a,hAK ha⟩
  let v : K c := ⟨k,hk⟩
  have hfix : MulAut.conj (f u) = 1 := by
    apply lineLocalSL_fixer_eq_one (by omega : 0<n) hF
    intro x hx
    obtain ⟨l,hl,rfl⟩ := hL.ge hx
    have hh : f ⁅u,l⁆ = 1 := hzero _ (hlocal (commutator_mem_commutator ha hl))
    change f u * f l * (f u)⁻¹ = f l
    apply mul_inv_eq_one.mp
    simpa only [commutatorElement_def,map_mul,map_inv] using hh
  have hh := DFunLike.congr_fun hfix (f v)
  have hz : f ⁅u,v⁆ = 1 := by
    simp only [commutatorElement_def,map_mul,map_inv]
    change (MulAut.conj (f u) (f v)) * (f v)⁻¹ = 1
    rw [hh]
    exact mul_inv_cancel _
  exact hback _ hz

/-- The whole doubled-natural row is impossible in the original source
configuration. The crossed core is localized by the actual normalizer action;
reciprocal commutators and the line-local fixer finish the contradiction. -/
theorem false_of_doubled {F : Type} [Field F] [Finite F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) : False := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨mark,hmodel,hline,_⟩ := whole_doubled_line_and_core D hf n hn hF e hm
  exact false_of_marked_doubled D hf n hn hF mark hmodel hline

/-- Original 4.3.10: the genuine whole-core alternatives select row (3),
with both original markings and no extra nonabelianity premise. The full
quotient recognition and whole-core classification remain explicit inputs. -/
theorem source_msData_of_alternatives
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hm : MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F.Carrier e) :
    ∃ d : MSData c n, d.field = F ∧
      (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier := by
  exact (source_doubled_or_msData D hf hb n hn F hdegree e P hP hm).resolve_left
    (fun hd => false_of_doubled D hf n hn
      (F.card_eq.trans (congrArg (2^·) hdegree)) e hd.1)

/-- Apply the selected third row to the original secondary component and
its quadratic root-normalizer orbit. Strict secondary-core enlargement is
still required for the final nonblock contradiction. -/
theorem source_component_of_alternatives
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hm : MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F.Carrier e) :
    ∃ B : Subgroup (rootNormalizer c),
      B.IsCComponent ∧ B.Normal ∧ IsQuasisimple (B ⧸ pCore 2 B) ∧
      secondary c < B.map (rootNormalizer c).subtype ∧
      B.map (rootNormalizer c).subtype ≤ Subgroup.centralizer (root c : Set G) ∧
      U c < rootCoreLayer c ∧
      rootCoreLayer c ≤ (B.map (rootNormalizer c).subtype).pCoreIn 2 ∧
      (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c ∧
      (frattini (rootCoreLayer c)).map (rootCoreLayer c).subtype ≤ root c ∧
      ⁅rootCoreLayer c,rootCoreLayer c⁆ ≤ root c := by
  obtain ⟨d,_,hL,_⟩ := source_msData_of_alternatives D hf hb n hn F hdegree e P hP hm
  exact d.exists_sourceComponent_of_line_marking hn D h hL

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledMarking
