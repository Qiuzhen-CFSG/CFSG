module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Setup
public import CFSG.Quasithin.Chapter1.Section03.Basic
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The primitive residual and its intrinsic Ξ action

The projection H → H/O₂(H), restricted to O²(H), has two-core kernel.
Its quotient is the literal odd residual in H/O₂(H). For an elementary
minimal normal plane, this identification transports irreducibility of
Sylow conjugation to the iterated Frattini quotient required by Ξ.

`PrimitiveResidual` records only the earlier primitive H=PT reduction;
it contains neither a closure classification nor Fitting containment.
The actual source application and the minimal-solvable producer are in
`Closure.Source`.

Source: Aschbacher--Smith, the paragraph before 14.6.12 on pp.1030--1031,
and the application of 1.3.4 on p.1033.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- The actual residual quotient, with its original projection retained. -/
theorem residual_quotient_equiv {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (H : Subgroup G) (hp : IsPGroup p (pResidual 2 (H ⧸ pCore 2 H))) :
    ∃ e : XiQuotient (residual H) ≃* pResidual 2 (H ⧸ pCore 2 H),
      ∀ x : residual H,
        (e (QuotientGroup.mk' (pCore 2 (residual H)) x) : H ⧸ pCore 2 H) =
          QuotientGroup.mk' (pCore 2 H) ⟨(x : G),residual_le H x.property⟩ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := pResidual 2 (H ⧸ pCore 2 H)
  have him : (pResidual 2 H).map q = R :=
    map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)
  let f : residual H →* R := {
    toFun x := ⟨q ⟨(x : G), residual_le H x.property⟩, by
      rw [← him]
      obtain ⟨y,hy,he⟩ := x.property
      exact mem_map.mpr ⟨y,hy,congrArg q (Subtype.ext he)⟩⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' x y := Subtype.ext (map_mul q
      ⟨(x : G),residual_le H x.property⟩ ⟨(y : G),residual_le H y.property⟩) }
  have hf : Function.Surjective f := by
    intro r
    have hr : (r : H ⧸ pCore 2 H) ∈ (pResidual 2 H).map q := by
      rw [him]; exact r.property
    obtain ⟨x,hx,he⟩ := mem_map.mp hr
    exact ⟨⟨x,mem_map_of_mem H.subtype hx⟩,Subtype.ext he⟩
  let i := inclusion (residual_le H)
  have hk : f.ker = (pCore 2 H).comap i := by
    ext x
    exact (Subtype.ext_iff.trans (QuotientGroup.eq_one_iff _))
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective i (inclusion_injective _)
  have hc : pCore 2 R = ⊥ := by
    have hd := IsPGroup.disjoint_of_coprime (pCore_isPGroup (p := 2))
      (hp.to_subgroup ⊤) ho.coprime_two_left
    simpa using hd
  have hker : f.ker = pCore 2 (residual H) := by
    simpa only [hc,MonoidHom.comap_bot] using f.comap_pCore_of_ker_isPGroup hf hkp
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨e,fun _ => rfl⟩

/-- Literal primitive input: the odd elementary residual of H/O₂(H) is
minimal normal, as in the replacement H=PT on printed pp.1030--1031. -/
structure PrimitiveResidual (H : Subgroup G) (p : ℕ) : Prop where
  elementary : IsElementaryAbelian p (pResidual 2 (H ⧸ pCore 2 H))
  minimal : ∀ B : Subgroup (H ⧸ pCore 2 H), B.Normal →
    B ≤ pResidual 2 (H ⧸ pCore 2 H) → B = ⊥ ∨ B = pResidual 2 (H ⧸ pCore 2 H)

/-- The primitive plane is a genuine member of Ξ with the original Sylow
conjugation on its intrinsic two-core and Frattini quotients. -/
theorem residual_mem_Xi (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hH : H ∈ Chapter1.H G)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (d : PrimitiveResidual H p)
    (hc : Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = p^2) :
    residual H ∈ Xi G (T : Subgroup G) := by
  let R := pResidual 2 (H ⧸ pCore 2 H)
  let := d.elementary
  obtain ⟨e,he⟩ := residual_quotient_equiv ho H (IsElementaryAbelian.isPGroup p R)
  let : IsElementaryAbelian p (XiQuotient (residual H)) :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  let : Fact (IsPGroup p (XiQuotient (residual H))) := ⟨IsElementaryAbelian.isPGroup p _⟩
  let eF := (frattiniQuotientEquivOfIsElementaryAbelian (p := p)).trans e
  have heF : ∀ x : residual H,
      (eF (QuotientGroup.mk' (frattini (XiQuotient (residual H)))
        (QuotientGroup.mk' (pCore 2 (residual H)) x)) : H ⧸ pCore 2 H) =
          QuotientGroup.mk' (pCore 2 H) ⟨(x : G),residual_le H x.property⟩ := fun x => he x
  have hHN : H ≤ normalizer (residual H : Set G) := le_normalizer_embedded_pResidual 2 H
  have hn := hTH.trans hHN
  have hgen : residual H ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
    simpa only [Chapter15.Section03.AbelianAmalgam.GenerationOne.residual,Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
      ← MonoidHom.range_eq_map,range_subtype] using hh
  refine ⟨isPPerfect_embedded_pResidual 2 H,hn,hgen.symm ▸ hH,
    ⟨p,Fact.out,ho,Or.inl ⟨inferInstance,(Nat.card_congr e.toEquiv).trans hc⟩⟩,?_⟩
  intro A hA
  let B := (A.map eF.toMonoidHom).map R.subtype
  have hBT : ((T : Subgroup G).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≤
      normalizer (B : Set (H ⧸ pCore 2 H)) := by
    apply le_normalizer_iff.mpr
    rintro t ⟨t,ht,rfl⟩ b ⟨b,⟨a,ha,rfl⟩,rfl⟩
    have hcompat : (eF (xiFrattiniAction (T : Subgroup G) (residual H) hn
        ⟨(t : G),ht⟩ a) : H ⧸ pCore 2 H) =
        QuotientGroup.mk' (pCore 2 H) t * (eF a : H ⧸ pCore 2 H) *
          (QuotientGroup.mk' (pCore 2 H) t)⁻¹ := by
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (frattini (XiQuotient (residual H))) a
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (residual H)) a
      unfold xiFrattiniAction
      simp only [MonoidHom.coe_comp,Function.comp_apply,quotientAut_apply_mk]
      rw [heF,heF,← map_inv,← map_mul,← map_mul]
      rfl
    change QuotientGroup.mk' (pCore 2 H) t * (eF a : H ⧸ pCore 2 H) *
      (QuotientGroup.mk' (pCore 2 H) t)⁻¹ ∈ B
    rw [← hcompat]
    exact mem_map_of_mem R.subtype (mem_map_of_mem eF.toMonoidHom (hA _ a ha))
  have hBR : B ≤ R := map_subtype_le _
  have hRB : R ≤ normalizer (B : Set (H ⧸ pCore 2 H)) :=
    ((le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative R)).trans
      (centralizer_le hBR)).trans (centralizer_le_normalizer _)
  have htop := pResidual_sup_sylow_eq_top
    ((T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)))
  have hBn : B.Normal := normalizer_eq_top_iff.mp
    (top_unique (htop ▸ sup_le hRB hBT))
  rcases d.minimal B hBn hBR with hb | hb
  · exact Or.inl ((map_eq_bot_iff_of_injective _ eF.injective).mp
      ((map_eq_bot_iff_of_injective _ R.subtype_injective).mp hb))
  · right
    apply A.eq_top_of_card_eq
    calc
      Nat.card A = Nat.card B := ((card_map_of_injective R.subtype_injective).trans
        (card_map_of_injective eF.injective)).symm
      _ = Nat.card R := hb ▸ rfl
      _ = Nat.card (XiFrattiniQuotient (residual H)) := (Nat.card_congr eF.toEquiv).symm

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
