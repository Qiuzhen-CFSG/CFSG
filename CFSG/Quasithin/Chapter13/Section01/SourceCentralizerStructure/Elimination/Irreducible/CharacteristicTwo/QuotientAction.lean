module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.LinearThreeMarking
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge
public import Theory.GroupAction.NormalizerFrattiniRelativeImage
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# The linear-three obstruction on the actual core quotient

For Q = K/O₂(K), the intersection N_G(K) ∩ N_G(X) acts on Q. Its restriction
to K induces inner automorphisms. The odd complement of X embeds in Q and
then Inn(Q) when its prime is coprime to |Z(Q)|. The original component Sylow
maps to a Sylow of Inn(Q), still normalizing the actual image of X.

A projective linear-three model of Q/Z(Q) now supplies the full-unipotent
marking for this solvable image. The root-scalar theorem contradicts the
transported irreducible relative normalizer action. No identification of K,
Q or Q/Z(Q), and no parabolic marking, is assumed.
Source: Aschbacher–Smith, 13.1.12(3), printed pp.874–875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination

open scoped MatrixGroups
open Chapter1 Chapter1.XiEmbedding
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3Even.UnipotentGeometry

private theorem conj_kernel (Q : Type*) [Group Q] :
    (MulAut.conj : Q →* MulAut Q).ker = center Q := by
  ext x
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    have hy := DFunLike.congr_fun hx y
    change x * y * x⁻¹ = y at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm
  · intro hx
    apply MulEquiv.ext
    intro y
    change x * y * x⁻¹ = y
    rw [← mem_center_iff.mp hx y, mul_inv_cancel_right]

/-- The inner group is the central quotient of Q, not Q itself. -/
private def innerCentralQuotientEquiv (Q : Type*) [Group Q] :
    MulAut.innerSubgroup Q ≃* (Q ⧸ center Q) :=
  (QuotientGroup.quotientKerEquivRange (MulAut.conj : Q →* MulAut Q)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (conj_kernel Q))

/-- The actual normalizer intersection acts on the component core quotient. -/
private def normalizerCoreAction {G : Type*} [Group G] (K X : Subgroup G) :
    (normalizer (K : Set G) ⊓ normalizer (X : Set G) : Subgroup G) →*
      MulAut (XiQuotient K) :=
  (quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion inf_le_left))

private theorem normalizerCoreAction_of_mem_component {G : Type*} [Group G]
    (K X : Subgroup G)
    (g : (normalizer (K : Set G) ⊓ normalizer (X : Set G) : Subgroup G))
    (hg : (g : G) ∈ K) :
    normalizerCoreAction K X g = MulAut.conj (QuotientGroup.mk' (pCore 2 K) ⟨g,hg⟩) := by
  ext q
  induction q using QuotientGroup.induction_on with | H q =>
    change quotientAut (pCore 2 K)
      (K.normalizerMonoidHom (inclusion inf_le_left g))
      (QuotientGroup.mk' (pCore 2 K) q) = _
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (pCore 2 K) (⟨g,hg⟩ * q * (⟨g,hg⟩ : K)⁻¹) = _
    simp only [map_mul,map_inv,MulAut.conj_apply]
    rfl

/-- Oddness removes the two-core kernel; the actual coprime center bound
removes the remaining central kernel. -/
private theorem normalizerCoreAction_injective_on_odd
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K X P : Subgroup G) (hPK : P ≤ K)
    (hPN : P ≤ normalizer (K : Set G) ⊓ normalizer (X : Set G))
    (hP : IsPGroup p P) (ho : Odd p)
    (hz : Nat.Coprime p (Nat.card (center (XiQuotient K)))) :
    Function.Injective ((normalizerCoreAction K X).comp (inclusion hPN)) := by
  let j := InvariantLarge.componentMap hPK
  have hj : Function.Injective j := InvariantLarge.componentMap_injective hP ho hPK
  have hker : Nat.Coprime p (Nat.card (MulAut.conj : XiQuotient K →*
      MulAut (XiQuotient K)).ker) := by rw [conj_kernel]; exact hz
  have hconj := injective_comp_subtype_of_coprime_ker
    (MulAut.conj : XiQuotient K →* MulAut (XiQuotient K)) hker j.range
    (hP.of_surjective j.rangeRestrict j.rangeRestrict_surjective)
  intro a b hab
  apply hj
  have hk (a : P) : (⟨(inclusion hPN a : G), hPK a.property⟩ : K) = inclusion hPK a := by
    apply Subtype.ext
    simp only [coe_inclusion]
  have he : MulAut.conj (j a) = MulAut.conj (j b) := by
    simpa only [j,InvariantLarge.componentMap,MonoidHom.comp_apply,normalizerCoreAction_of_mem_component K X
      (inclusion hPN a) (hPK a.property),normalizerCoreAction_of_mem_component K X
      (inclusion hPN b) (hPK b.property),hk] using hab
  have hr : j.rangeRestrict a = j.rangeRestrict b := hconj he
  exact congrArg Subtype.val hr

/-- The unipotent marking only needs the original noncyclic odd complement,
not a claim identifying the whole radical with its quotient. -/
private theorem noncyclic_actor_row_excluded_of_sylow
    {G : Type*} [Group G] [Finite G]
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] (hn : 2 ≤ n) (hF : Nat.card F = 2^n) (ho : Odd p)
    (X P K : Subgroup G) [Group.IsSolvable X]
    (hPX : P ≤ X) (hXK : X ≤ K) (hP : XiOddQuotient p P)
    (hirr : IsNormalizerFrattiniIrreducible (P.subgroupOf (normalizer X)))
    (e : K ≃* PSL(3,F)) (S : Sylow 2 K)
    (hSX : (S : Subgroup K).map K.subtype ≤ normalizer (X : Set G)) : False := by
  let Y := X.subgroupOf K
  let Q := P.subgroupOf K
  have hPK := hPX.trans hXK
  let : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hXK).toMonoidHom) (subgroupOfEquivOfLe hXK).injective
  have hSY : (S : Subgroup K) ≤ normalizer (Y : Set K) := by
    intro s hs
    exact X.le_normalizer_comap K.subtype (hSX (mem_map_of_mem K.subtype hs))
  obtain ⟨f,hf⟩ := UnipotentCore.exists_unipotent_marking F hn hF ho e S Y Q
    (subgroupOf_mono K hPX) hP.isPGroup.comap_subtype
    (fun hc => hP.not_isCyclic ((subgroupOfEquivOfLe hPK).isCyclic.mp hc)) hSY
  have hc : Y.pCoreIn 2 = (X.pCoreIn 2).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_pCoreIn_of_injective 2 Y K.subtype K.subtype_injective]
    change (X.subgroupOf K |>.map K.subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le hXK,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hXK)]
  have hA : ((X.pCoreIn 2).subgroupOf K).map f.toMonoidHom = unipotent F := hc ▸ hf
  have hXA : X ≤ normalizer (X.pCoreIn 2 : Set G) :=
    X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hnK : X.subgroupOf K ≤ normalizer ((X.pCoreIn 2).subgroupOf K : Set K) :=
    (comap_mono hXA).trans ((X.pCoreIn 2).le_normalizer_comap K.subtype)
  have hXB : (X.subgroupOf K).map f.toMonoidHom ≤ borel F := by
    have hh := (map_mono (f := f.toMonoidHom) hnK).trans
      (((X.pCoreIn 2).subgroupOf K).le_normalizer_map f.toMonoidHom)
    rwa [hA,normalizer_unipotent F (by omega) hF] at hh
  exact SourceCentralizerComponents.source_linearThree_twoCore_row_excluded F hF ho
    X K P hPX hXK f ((map_mono (subgroupOf_mono K hPX)).trans hXB) hA hP hirr

/-- A quotient map that embeds the odd complement preserves the concrete
scalar-action contradiction. The target Sylow subgroup and component model
must be constructed from the original component; they are not inferred here. -/
private theorem image_actor_row_excluded_of_sylow
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (X P : Subgroup G) [Group.IsSolvable X]
    (hPX : P ≤ X) (hf : Function.Injective (f.comp P.subtype))
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] (hn : 2 ≤ n) (hF : Nat.card F = 2^n) (ho : Odd p)
    (hP : XiOddQuotient p P)
    (hirr : IsNormalizerFrattiniIrreducible (P.subgroupOf (normalizer X)))
    (K : Subgroup H) (hXK : X.map f ≤ K) (e : K ≃* PSL(3,F))
    (S : Sylow 2 K) (hSX : (S : Subgroup K).map K.subtype ≤ normalizer (X.map f)) : False := by
  let j : P ≃* P.map f := MulEquiv.ofBijective (f.subgroupMap P)
    ⟨fun a b hab => hf (congrArg Subtype.val hab), f.subgroupMap_surjective P⟩
  let : Group.IsSolvable (X.map f) := Group.isSolvable_of_surjective
    (f.subgroupMap_surjective X)
  exact noncyclic_actor_row_excluded_of_sylow F hn hF ho (X.map f) (P.map f) K
    (map_mono hPX) hXK (hP.of_mulEquiv j)
    (irreducible_map_relative_normalizer f X P hPX hf hirr) e S hSX

/-- The scalar obstruction on the actual component core quotient. Both the
conjugation kernel and the image of the component Sylow are constructed. -/
theorem core_quotient_linearThree_excluded
    {G : Type*} [Group G] [Finite G]
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] (hn : 2 ≤ n) (hF : Nat.card F = 2^n) (ho : Odd p)
    (X M K : Subgroup G) (hXM : X ≤ M) (hMX : M ≤ normalizer X)
    (hMK : M ≤ normalizer K) (hXK : X ≤ K)
    (hq : XiOddQuotient p (XiQuotient X))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : M, ∀ a ∈ A, xiFrattiniAction M X hMX s a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hz : Nat.Coprime p (Nat.card (center (XiQuotient K))))
    (e : (XiQuotient K ⧸ center (XiQuotient K)) ≃* PSL(3,F))
    (S : Sylow 2 K) (hSX : (S : Subgroup K).map K.subtype ≤ normalizer (X : Set G)) :
    False := by
  let P : Sylow p X := default
  let P₀ := (P : Subgroup X).map X.subtype
  have hPX : P₀ ≤ X := map_subtype_le _
  have hP : XiOddQuotient p P₀ :=
    hq.of_mulEquiv (RadicalActions.ambientSylowQuotientEquiv ho hq.isPGroup P).symm
  let N := normalizer (K : Set G) ⊓ normalizer (X : Set G)
  have hXN : X ≤ N := le_inf (hXK.trans K.le_normalizer) X.le_normalizer
  have hPN : P₀ ≤ N := hPX.trans hXN
  have hMN : M ≤ N := le_inf hMK hMX
  let XN := X.subgroupOf N
  let PN := P₀.subgroupOf N
  let ep : PN ≃* P₀ := subgroupOfEquivOfLe hPN
  let : XN.Normal := (normal_subgroupOf_iff_le_normalizer hXN).mpr inf_le_right
  have hiPN : IsNormalizerFrattiniIrreducible PN :=
    normalizerFrattiniIrreducible_subgroupOf P₀ (M ⊓ normalizer (P₀ : Set G)) N
      hPN (inf_le_left.trans hMN) inf_le_right
      (RadicalActions.normalizer_irreducible hMX ((pCoreIn_le 2 X).trans hXM)
        hirr ho hq.isPGroup P)
  have hi : IsNormalizerFrattiniIrreducible (PN.subgroupOf (normalizer XN)) := by
    rw [XN.normalizer_eq_top]
    exact normalizerFrattiniIrreducible_subgroupOf PN (normalizer PN) ⊤
      le_top le_top le_rfl hiPN
  let : Group.IsSolvable X := by
    let : Group.IsNilpotent (XiQuotient X) := hq.isPGroup.isNilpotent
    let : Group.IsNilpotent (pCore 2 X) := pCore_isPGroup.isNilpotent
    exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr
      ⟨inferInstance,inferInstance⟩
  let : Group.IsSolvable XN := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hXN).toMonoidHom) (subgroupOfEquivOfLe hXN).injective
  let f := normalizerCoreAction K X
  have hf : Function.Injective (f.comp PN.subtype) := by
    have hj := normalizerCoreAction_injective_on_odd K X P₀
      (hPX.trans hXK) hPN hP.isPGroup ho hz
    intro a b hab
    apply ep.injective
    exact hj hab
  let Q := XiQuotient K
  let q := QuotientGroup.mk' (pCore 2 K)
  let g : K →* MulAut.innerSubgroup Q :=
    (MulAut.conj.comp q).codRestrict _ (fun k => ⟨q k,rfl⟩)
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨x,hx⟩ := a.property
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
    exact ⟨k,Subtype.ext hx⟩
  let S' : Sylow 2 (MulAut.innerSubgroup Q) := S.mapSurjective hg
  have hXI : XN.map f ≤ MulAut.innerSubgroup Q := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨q ⟨x,hXK hx⟩,(normalizerCoreAction_of_mem_component K X x (hXK hx)).symm⟩
  have hSI : (S' : Subgroup (MulAut.innerSubgroup Q)).map
      (MulAut.innerSubgroup Q).subtype ≤ normalizer (XN.map f) := by
    rintro _ ⟨a,ha,rfl⟩
    change a ∈ (S : Subgroup K).map g at ha
    obtain ⟨k,hk,rfl⟩ := ha
    have hkX : (k : G) ∈ normalizer X := hSX (mem_map_of_mem K.subtype hk)
    let kN : N := ⟨k,⟨K.le_normalizer k.property,hkX⟩⟩
    have hkN : kN ∈ normalizer XN := X.le_normalizer_comap N.subtype hkX
    have hh := XN.le_normalizer_map f (mem_map_of_mem f hkN)
    change f kN ∈ normalizer (XN.map f) at hh
    rw [normalizerCoreAction_of_mem_component K X kN k.property] at hh
    exact hh
  exact image_actor_row_excluded_of_sylow f XN PN (subgroupOf_mono N hPX) hf
    F hn hF ho (hP.of_mulEquiv ep.symm) hi (MulAut.innerSubgroup Q) hXI
    ((innerCentralQuotientEquiv Q).trans e) S' hSI

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
