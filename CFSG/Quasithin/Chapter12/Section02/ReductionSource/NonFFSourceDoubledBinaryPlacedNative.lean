module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedNative
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedNormality

/-!
# The complete binary doubled orbit in the actual J₄ or Ru carrier

The original placed component has trivial full center by the existing
odd-primary multiplier bounds and its original trivial two-core. Its native
isomorphism is the original quotient marking, composed with the literal
ambient inclusion. Transporting the whole orbit through that map retains its
order 64, both marked natural and dual axes, and the original residual action.

The orbit lies in the center of the residual image's intrinsic two-core and
is its own commutator with that residual image. Their native normalizers are
equal; this is the unique maximal two-local over the residual, and its full
preimage is exactly K intersect N_G(L). Both images are relatively normal
in every native two-local containing the residual. The final original-input
application retains the same H-star subgroup, odd actor and component, with
all earlier model exclusions and the separate maximal pushing-up witness.

These results discharge the simplicity and transport steps of the local
inspection in Aschbacher--Smith 4.4.3, printed pp.622--623, as used in 7.3.4
and 7.6.1. The native placed-row exclusions and the maximal pushing-up
contradiction remain to be proved; no full-Sylow placement is asserted.
Source: refs/quasithin.pdf. Existing public conditional APIs are preserved.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Representation Representation.BinaryOffender BinaryLinearThree
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Native placement keeps the full quotient map, original residual, both
marked axes and the complete natural-dual conjugation action. -/
@[expose] def BinaryPlacedNativeGeometry (A : Subgroup G)
    (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    {Q : Type*} [_root_.Group Q] (e : (K ⧸ center K) ≃* Q) : Prop :=
  center K = ⊥ ∧ IsSimpleGroup K ∧
  ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Q,
    (∀ x, m x = e (QuotientGroup.mk' (center K)
      ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
    let r := m.toMonoidHom.comp (inclusion hr)
    UniqueMaximalOvergroup r.range (normalizer (r.range : Set Q)) ∧
    (normalizer (r.range : Set Q)).comap m.toMonoidHom =
      (normalizer (L : Set G)).subgroupOf (K.map (normalizer (A : Set G)).subtype) ∧
    ∃ hWK : D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype,
      let w := m.toMonoidHom.comp (inclusion hWK)
      Nat.card w.range = 64 ∧
      w.range ≤ r.range.pCoreIn 2 ∧
      w.range ≤ centralizer (r.range.pCoreIn 2 : Set Q) ∧
      w.range = ⁅w.range,r.range⁆ ∧
      normalizer (w.range : Set Q) = normalizer (r.range : Set Q) ∧
      (∀ B : Subgroup Q, IsTwoLocal B → r.range ≤ B →
        (r.range.subgroupOf B).Normal ∧ w.range ≤ B ∧ (w.range.subgroupOf B).Normal) ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
        ∃ eR : (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) ≃* BinaryLinearThree.Group,
        ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
          (∀ x v, r x * w (E.symm v).toMul * (r x)⁻¹ =
            w (E.symm (NaturalDual.action (eR (QuotientGroup.mk' _ x)) v)).toMul) ∧
          (∀ v, (E v).2 = 0 ↔ (v.toMul : G) ∈ V) ∧
          (∀ v, (E v).1 = 0 ↔ (v.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom)

/-- The actual placed J₄/Ru component is simple, and the native local retains
the same whole marked orbit and residual action. -/
theorem sourceOrbit_binary_oddNormalizer_native_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (name : ClassificationModels.SporadicName) (hn : name = .j4 ∨ name = .ru)
    (e : (K ⧸ center K) ≃* name.Carrier) : D.BinaryPlacedNativeGeometry A K hr e := by
  let : IsQuasisimple K := hK.2
  have hz : center K = ⊥ := by
    apply DoubledBinaryPlacedNative.center_eq_bot hcore
    rcases hn with rfl | rfl
    · exact Or.inl ⟨e⟩
    · exact Or.inr ⟨e⟩
  let Q := name.Carrier
  let R := oddActorResidual L A
  let W := D.sourceOrbit
  let N := normalizer (A : Set G)
  let K₀ := K.map N.subtype
  let a : K₀ ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let m : K₀ ≃* Q := a.trans (DoubledBinaryPlacedNative.nativeEquiv hz e)
  let q := m.toMonoidHom
  let r := q.comp (inclusion hr)
  obtain ⟨_,hm,hWR,t,ht,hnt,qL,hqL,hker,eR,he,E,hE,hV,hVt⟩ :=
    D.sourceOrbit_binary_odd_residual_coordinates h hd F hF hmodel A hAC ho
  have hKN : K₀ ≤ N := map_subtype_le _
  have hcentermap : (center K₀).map a.toMonoidHom = center K := by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr a ⟨z,hz⟩).property
    · intro z hz
      exact ⟨a.symm z,(centerCongr a.symm ⟨z,hz⟩).property,a.apply_symm_apply z⟩
  let eK := (QuotientGroup.congr (center K₀) (center K) a hcentermap).trans e
  have hne : W ≠ ⊥ := D.sourceOrbit_weakClosure_setup.nontrivial
  have huQ : UniqueMaximalOvergroup r.range (normalizer (r.range : Set Q)) :=
    DoubledBinaryPlacedNormality.residual_image_unique_local hKN hr hu hWR hne hm eK
  have hp : (normalizer (r.range : Set Q)).comap q =
      (normalizer (L : Set G)).subgroupOf K₀ :=
    DoubledBinaryPlacedNormality.residual_normalizer_preimage hKN hr hu hWR hne hm eK
  have hWR' : W ≤ R := hWR.trans (pCoreIn_le 2 R)
  have hWK : W ≤ K₀ := hWR'.trans hr
  let w := q.comp (inclusion hWK)
  have hiw : Function.Injective w := m.injective.comp (inclusion_injective hWK)
  have hcard : Nat.card W = 64 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,
      D.sourceOrbit_binary_dimension h hd F hF hmodel] at hh
    exact hh
  have hcW : Nat.card w.range = 64 :=
    (Nat.card_congr (MonoidHom.ofInjective hiw).toEquiv).symm.trans hcard
  have hc : q.ker ≤ center K₀ := by
    rw [q.ker_eq_bot_iff.mpr m.injective]
    exact bot_le
  have hnormal (B : Subgroup Q) (hB : IsTwoLocal B) (hRB : r.range ≤ B) :
      (r.range.subgroupOf B).Normal ∧ w.range ≤ B ∧ (w.range.subgroupOf B).Normal := by
    exact ⟨(DoubledBinaryPlacedNormality.local_preimage_and_normality
      hKN hr hu q m.surjective hc B hB hRB).2,
      DoubledBinaryPlacedNormality.whole_module_normal_in_local hKN hr hu hWR'
        (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge q m.surjective hc B hB hRB⟩
  have hWN := hnormal (normalizer (r.range : Set Q)) huQ.1.1 r.range.le_normalizer
  have hNRW : normalizer (r.range : Set Q) ≤ normalizer (w.range : Set Q) :=
    (normal_subgroupOf_iff_le_normalizer hWN.2.1).mp hWN.2.2
  have hWne : w.range ≠ ⊥ := by
    intro heq
    rw [heq,card_bot] at hcW
    omega
  have hpw : IsPGroup 2 w.range := (IsElementaryAbelian.isPGroup 2 W).of_surjective
    w.rangeRestrict w.rangeRestrict_surjective
  have hNWlocal : IsTwoLocal (normalizer (w.range : Set Q)) := ⟨w.range,hWne,hpw,rfl⟩
  have hRW := r.range.le_normalizer.trans hNRW
  have hNWR := (normal_subgroupOf_iff_le_normalizer hRW).mp
    (hnormal (normalizer (w.range : Set Q)) hNWlocal hRW).1
  have hcomp (z : W) : r (inclusion hWR' z) = w z := rfl
  have haction (x : R) (v : NaturalDual.Space) :
      r x * w (E.symm v).toMul * (r x)⁻¹ =
        w (E.symm (NaturalDual.action (eR (QuotientGroup.mk' _ x)) v)).toMul := by
    have hact : doubledSeedAction R W
        (((oddActorResidual_le L A).trans inf_le_left).trans
          D.sourceOrbit_component_normalizes) x (E.symm v) =
        E.symm (NaturalDual.action (eR (QuotientGroup.mk' _ x)) v) := by
      apply E.injective
      rw [hE,E.apply_symm_apply,E.apply_symm_apply]
    have hh : x * inclusion hWR' (E.symm v).toMul * x⁻¹ =
        inclusion hWR' (E.symm (NaturalDual.action (eR (QuotientGroup.mk' _ x)) v)).toMul :=
      Subtype.ext (congrArg (fun z : Additive W => (z.toMul : G)) hact)
    have hf := congrArg r hh
    simpa only [map_mul,map_inv,hcomp] using hf
  let b : R ≃* r.range := MonoidHom.ofInjective (m.injective.comp (inclusion_injective hr))
  have hcoreMap : (pCore 2 R).map r = r.range.pCoreIn 2 := by
    change _ = (pCore 2 r.range).map r.range.subtype
    rw [←pCore_map_iso 2 b,map_map]
    rfl
  have hwcore : w.range ≤ r.range.pCoreIn 2 := by
    rw [←hcoreMap]
    rintro _ ⟨v,rfl⟩
    obtain ⟨x,hx,hxv⟩ := hWR v.property
    refine ⟨x,hx,?_⟩
    apply congrArg q
    exact Subtype.ext hxv
  have hwcentral : w.range ≤ centralizer (r.range.pCoreIn 2 : Set Q) := by
    rw [←hcoreMap]
    rintro _ ⟨v,rfl⟩ _ ⟨x,hx,rfl⟩
    have hh := haction x (E (Additive.ofMul v))
    have hxq : QuotientGroup.mk' (pCore 2 (oddActorResidual L A)) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    simp only [hxq,map_one,Module.End.one_apply,E.symm_apply_apply] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hwm : (W.subgroupOf K₀).map q = w.range := by
    rw [←inclusion_range hWK,←MonoidHom.range_comp]
  have hrm : (R.subgroupOf K₀).map q = r.range := by
    rw [←inclusion_range hr,←MonoidHom.range_comp]
  have hmK : W.subgroupOf K₀ = ⁅W.subgroupOf K₀,R.subgroupOf K₀⁆ := by
    apply Subgroup.map_injective K₀.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWK,map_subgroupOf_eq_of_le hr]
    exact hm
  have hmove : w.range = ⁅w.range,r.range⁆ := by
    have hh := congrArg (fun B : Subgroup K₀ => B.map q) hmK
    rwa [map_commutator,hwm,hrm] at hh
  exact ⟨hz,DoubledBinaryPlacedNative.isSimpleGroup hz,m,fun _ => rfl,huQ,hp,
    hWK,hcW,hwcore,hwcentral,hmove,le_antisymm hNWR hNRW,hnormal,
    t,ht,hnt,eR,E,haction,hV,hVt⟩

/-- The original placed alternative, retaining every earlier clause and the
native geometry on that very component and quotient marking. -/
@[expose] def BinaryPlacedNativeCase (A : Subgroup G) : Prop :=
  UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 p) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 p)) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 (p^2)) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 (p^2))) ∧
    (K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      ∃ hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype,
      centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
      6 ≤ primeRank 2 (K ⧸ center K) ∧
      ¬ ChapterA.Section02.IsTheoremBOddModel (K ⧸ center K) ∧
      DoubledBinaryPlacedLocals.LocalData (K ⧸ center K) ∧
      (∃ name : ClassificationModels.SporadicName,
          (name = .j4 ∨ name = .ru) ∧
          ∃ e : (K ⧸ center K) ≃* name.Carrier, D.BinaryPlacedNativeGeometry A K hr e) ∧
      (∀ p : ℕ, (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) →
        ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 p) ∧
      ∃ j : oddActorResidual L A →* K ⧸ center K, IsPGroup 2 j.ker ∧
        ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f)

/-- Discharge the native geometry from the original chosen-module hypotheses
on the same witness selected by the placed-component reduction. -/
theorem sourceOrbit_binary_placed_native_case
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hc : D.BinaryPlacedJankoRudvalisCase A) :
    D.BinaryPlacedNativeCase A := by
  obtain ⟨hu,K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,
    hn,hW,hr,hC,hrank,hodd,hl,⟨name,hname,⟨e⟩⟩,hfour,j,hj,f,hf⟩ := hc
  exact ⟨hu,K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,
    hn,hW,hr,hC,hrank,hodd,hl,
    ⟨name,hname,e,D.sourceOrbit_binary_oddNormalizer_native_placement
      h hd F hF hmodel A hAC ho hu K hK hcore hr name hname e⟩,hfour,j,hj,f,hf⟩

/-- Original-input application: the surviving H-star obstruction has either
the literal maximal pushing-up pair or the same now-simple native component,
with the complete marked natural-dual action and relative local normality. -/
theorem sourceOrbit_binary_native_oddLocal_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ((∃ J P : Subgroup G,
          J ∈ muStar (normalizer (L : Set G)) L
            (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
          PushLE L (oddActorResidual L A) J ∧
          IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
          IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
        D.BinaryPlacedNativeCase A) := by
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hcases⟩ :=
    D.sourceOrbit_binary_placed_oddLocal_obstruction h hd hmany hnon F hF hmodel
  refine ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  rcases hcases with hpush | ⟨hplaced,_⟩
  · exact Or.inl hpush
  · exact Or.inr (D.sourceOrbit_binary_placed_native_case h hd F hF hmodel A hAC
      (hcard.symm ▸ hpo) hplaced)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
