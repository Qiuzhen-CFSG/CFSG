module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.QuotientStabilizer
public import Theory.GroupTheory.PCoreSurjective

/-!
# The actual central-model maps in the escaping-component branch

These maps retain K, K/O₂(K), and its central quotient as separate carriers.
Odd-primary injectivity and a two-core preimage identity control the kernels;
conjugation equivariance transports the original C_L(u) action. The Sp₄ and
G₂ source exclusions both use these identities on the canonical radical.

Source: Aschbacher–Smith, 13.1.12(3), printed pp.874–875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve
variable {G : Type*} [Group G] [Finite G]

/-- The actual successive two-core and central quotient maps, followed by the model. -/
@[expose] noncomputable def componentCentralModelMap (K : Subgroup G)
    {D : Type*} [Group D] (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* D) : K →* D :=
  j.toMonoidHom.comp ((QuotientGroup.mk' (center (XiQuotient K))).comp
    (QuotientGroup.mk' (pCore 2 K)))

omit [Finite G] in
/-- Equivariance for the actual two successive quotient maps. -/
theorem componentCentralModelMap_conjugate (K : Subgroup G)
    {D : Type*} [Group D] (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* D)
    (a : normalizer (K : Set G)) (x : K) :
    componentCentralModelMap K j (K.normalizerMonoidHom a x) =
      MulAut.centralQuotientAction j (quotientAut (pCore 2 K) (K.normalizerMonoidHom a))
        (componentCentralModelMap K j x) := by
  change _ = MulAut.centralQuotientAction j _
    (j (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)))
  rw [MulAut.centralQuotientAction_apply,quotientAut_apply_mk]
  rfl

/-- Odd-primary subgroups survive the two-core and coprime central kernels. -/
theorem componentCentralModelMap_injective_odd {p : ℕ} [Fact p.Prime]
    (K P : Subgroup G) (hPK : P ≤ K) (hP : IsPGroup p P) (hp : Odd p)
    (hz : Nat.Coprime p (Nat.card (center (XiQuotient K))))
    {D : Type*} [Group D] (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* D) :
    Function.Injective ((componentCentralModelMap K j).comp (inclusion hPK)) := by
  let f := InvariantLarge.componentMap hPK
  have hf : Function.Injective f := InvariantLarge.componentMap_injective hP hp hPK
  let q := QuotientGroup.mk' (center (XiQuotient K))
  have hk : Nat.Coprime p (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']; exact hz
  have hq := injective_comp_subtype_of_coprime_ker q hk f.range
    (hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  intro a b hab
  apply hf
  have he : q (f a) = q (f b) := j.injective hab
  exact congrArg Subtype.val (hq (a₁ := f.rangeRestrict a) (a₂ := f.rangeRestrict b) he)

variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The literal stabilizer action preserves the canonical radical image in a central model. -/
theorem Context.model_stabilizer_preserves_radical (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    {D : Type*} [Group D] [Finite D]
    (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* D)
    (a : (L ⊓ centralizer ({u} : Set G) : Subgroup G)) :
    let q := componentCentralModelMap K j
    let τ := (MulAut.centralQuotientAction j).comp
      (componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi))
    (((XiP p L).subgroupOf K).map q).map (τ a).toMonoidHom =
      ((XiP p L).subgroupOf K).map q := by
  dsimp only
  let q := componentCentralModelMap K j
  let τ := (MulAut.centralQuotientAction j).comp
    (componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi))
  let Y := ((XiP p L).subgroupOf K).map q
  change Y.map (τ a).toMonoidHom = Y
  have hc : Nat.card (Y.map (τ a).toMonoidHom) = Nat.card Y :=
    card_map_of_injective (τ a).injective
  apply eq_of_le_of_card_ge ?_ hc.ge
  rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
  let b := K.normalizerMonoidHom
    (inclusion (h.stabilizer_normalizes_component s e hi) a)
  have hbx : b x ∈ (XiP p L).subgroupOf K := by
    exact (mem_normalizer_iff.mp (XiP_invariant p L.le_normalizer a.property.1) x).mp hx
  refine ⟨b x,hbx,?_⟩
  change q (b x) = MulAut.centralQuotientAction j
    (componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi) a)
      (j (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)))
  rw [MulAut.centralQuotientAction_apply]
  change q (b x) = j (QuotientGroup.mk' _
    (quotientAut (pCore 2 K) b (QuotientGroup.mk' _ x)))
  rw [quotientAut_apply_mk]
  rfl

/-- A model equivalence induces the actual equivalence of central quotients. -/
noncomputable def componentModelCenterCongruence {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve
variable {G : Type*} [Group G] [Finite G]

/-- Pulling the model two-core back recovers the canonical radical two-core. -/
theorem componentCentralModelMap_core_preimage {p : ℕ} [Fact p.Prime]
    (X K : Subgroup G) (hXK : X ≤ K)
    (hshape : XiOddQuotient p (XiQuotient X))
    (hz : Nat.Coprime p (Nat.card (center (XiQuotient K))))
    (hz2 : Nat.Coprime 2 (Nat.card (center (XiQuotient K))))
    {D : Type*} [Group D] [Finite D]
    (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* D) :
    let f := (componentCentralModelMap K j).comp (inclusion hXK)
    (pCore 2 f.range).comap f.rangeRestrict = pCore 2 X := by
  let v := InvariantLarge.componentMap hXK
  let f := (componentCentralModelMap K j).comp (inclusion hXK)
  have hcard : Nat.Coprime (Nat.card X) (Nat.card (center (XiQuotient K))) := by
    obtain ⟨a,ha⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
    obtain ⟨b,hb⟩ := hshape.isPGroup.exists_card_eq
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 X),ha,hb]
    exact (hz.pow_left b).mul_left (hz2.pow_left a)
  have hd : Disjoint v.range (center (XiQuotient K)) :=
    disjoint_of_coprime_natCard (hcard.of_dvd_left
      (card_dvd_of_surjective v.rangeRestrict v.rangeRestrict_surjective))
  have hv : IsPGroup 2 v.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hXK)).ker)
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective (inclusion hXK) (inclusion_injective hXK)
  have hle : f.ker ≤ v.ker := by
    intro x hx
    change v x = 1
    apply hd.le_bot
    refine ⟨⟨x,rfl⟩,?_⟩
    apply (QuotientGroup.eq_one_iff _).mp
    exact j.injective (hx.trans j.map_one.symm)
  have hk : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hv.to_le hle
  exact f.rangeRestrict.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective hk

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
