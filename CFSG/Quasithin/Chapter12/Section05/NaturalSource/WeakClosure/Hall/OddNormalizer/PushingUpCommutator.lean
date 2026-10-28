module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpComponentEquality
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicResidual.TwoCentralizer
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import CFSG.Quasithin.Chapter4.Section02

/-!
# Fixed exterior vectors and the cubic commutator obstruction

The full J₄ cover injects the original exterior module into its central
quotient: a vector in the covering center would be fixed by the covering
intersection residual, hence by L, contrary to the exterior fixed-space
calculation. The native cubic-residual centralizer bound therefore gives
a vector among the sixteen original cubic-fixed vectors which is moved by
the entire residual, retaining its actual ambient inclusion.

The covered exterior action is irreducible on ambient subgroups. Thus a
nonzero central commutator image from a binary subgroup normalized by the
intersection residual would equal V. Coprime action supplies an actual
cubic-fixed preimage of the moved vector. Normality of the full residual
in C_G(x), already proved, contradicts this lift. We conclude that every
such central commutator image vanishes.

The source still requires construction of R₁ and an appropriate involution
whose commutators lie in V and have nonzero image. The separate odd-local
comparison on p.623 is also retained. All full covers, quotient maps,
relative placements, and the original exterior module are unchanged.
Source: Aschbacher--Smith, 4.2.13, printed p.612. The Hall application is
in OddNormalizer, using 12.2.11(a), printed pp.798--799.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter7.NormalizedSource.MathieuGeneration
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in
private theorem cover_module_quotient_injective
    (s : SylowExteriorMarking D)
    {F K : Subgroup G} (hVK : V ≤ K) (hFK : F ≤ K)
    (hcover : (L : Set G) = (F : Set G) * (L.pCoreIn 2 : Set G)) :
    Function.Injective ((QuotientGroup.mk' (center K)).comp (inclusion hVK)) := by
  let f := (QuotientGroup.mk' (center K)).comp (inclusion hVK)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_bot_iff.mp
  intro x hx
  have hz : inclusion hVK x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hxc : (x : G) ∈ centralizer (F : Set G) := by
    intro y hy
    exact congrArg K.subtype (mem_center_iff.mp hz (inclusion hFK ⟨y,hy⟩))
  have hxl : (x : G) ∈ centralizer (L : Set G) := by
    intro y hy
    obtain ⟨a,ha,b,hb,rfl⟩ := hcover ▸ (show y ∈ (L : Set G) from hy)
    calc
      (a * b) * (x : G) = a * (b * x) := mul_assoc _ _ _
      _ = a * (x * b) := congrArg (a * ·) ((hcore hb) x x.property).symm
      _ = x * (a * b) := by rw [←mul_assoc,hxc a ha,mul_assoc]
  apply Subtype.ext
  exact (show (x : G) ∈ (⊥ : Subgroup G) from s.marking.fixed_eq_bot ▸ ⟨x.property,hxl⟩)

/-- A vector fixed by the original cubic is moved by the full cubic residual.
The original covering component and the entire exterior module are retained. -/
theorem exterior_pushingUp_cubic_fixed_vector_moved
    (s : SylowExteriorMarking D)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) (k : K) (hk : orderOf k = 3)
    (hfix : 16 ≤ Nat.card (V ⊓ centralizer ({((k : H) : G)} : Set G) : Subgroup G)) :
    let Rg := (solvableResidual (centralizer ({k} : Set K))).map
      (H.subtype.comp (K.subtype.comp (centralizer ({k} : Set K)).subtype))
    ∃ v ∈ V, v ∈ centralizer ({((k : H) : G)} : Set G) ∧
      v ∉ centralizer (Rg : Set G) := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Kg := K.map H.subtype
  have hc := hw.2.2.2.2.2.2.1
  have hcover := hw.2.2.2.2.2.2.2.1
  have hVF := hw.2.2.2.2.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hVK : V ≤ Kg := hVF.trans hFK
  let eg : Kg ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let eq := (centerQuotientCongr eg).trans e
  let q := eq.toMonoidHom.comp (QuotientGroup.mk' (center Kg))
  have hq : Function.Surjective q := eq.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = center Kg :=
    (MonoidHom.ker_comp_of_injective _ _ eq.injective).trans (QuotientGroup.ker_mk' _)
  let : K.Normal := hc.ordinary_component_normal K hK
  have hthree : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [hqker,Nat.card_congr (centerCongr eg).toEquiv]
    exact pushingUp_component_center_three_coprime hw K
  let x : Kg := eg.symm k
  have hx : orderOf x = 3 := (eg.symm.orderOf_eq k).trans hk
  let P := V ⊓ centralizer ({((k : H) : G)} : Set G)
  have hPK : P ≤ Kg := inf_le_left.trans hVK
  have hi : Function.Injective (q.comp (P.subgroupOf Kg).subtype) := by
    intro a b he
    have he' : ((QuotientGroup.mk' (center Kg)).comp (inclusion hVK))
        ⟨a.val.val,a.property.1⟩ =
        ((QuotientGroup.mk' (center Kg)).comp (inclusion hVK)) ⟨b.val.val,b.property.1⟩ :=
      eq.injective he
    have hv := cover_module_quotient_injective s hVK hFK hcover he'
    exact Subtype.ext (Subtype.ext (congrArg V.subtype hv))
  dsimp only
  by_contra hn
  push Not at hn
  have hPC : P.subgroupOf Kg ≤ centralizer
      ((solvableResidual (centralizer ({x} : Set Kg))).map
        (centralizer ({x} : Set Kg)).subtype : Set Kg) := by
    intro p hp z hz
    obtain ⟨c,hc,rfl⟩ := hz
    let j : centralizer ({x} : Set Kg) →* centralizer ({k} : Set K) := {
      toFun c := ⟨eg c,mem_centralizer_singleton_iff.mpr (by
        have hh := congrArg eg (mem_centralizer_singleton_iff.mp c.property)
        simpa only [map_mul,x,eg.apply_symm_apply] using hh)⟩
      map_one' := Subtype.ext (map_one eg)
      map_mul' a b := Subtype.ext (map_mul eg (a : Kg) (b : Kg)) }
    have hmap : j c ∈ solvableResidual (centralizer ({k} : Set K)) :=
      map_solvableResidual_le j (mem_map_of_mem j hc)
    have hv := hn p.val hp.1 hp.2
    have hm := hv _ (mem_map_of_mem
      (H.subtype.comp (K.subtype.comp (centralizer ({k} : Set K)).subtype)) hmap)
    have heg : ((eg c.val : H) : G) = (c.val : G) :=
      congrArg Kg.subtype (eg.symm_apply_apply c.val)
    apply Subtype.ext
    change ((eg c.val : H) : G) * (p : G) = (p : G) * ((eg c.val : H) : G) at hm
    change (c.val : G) * (p : G) = (p : G) * (c.val : G)
    simpa only [heg] using hm
  have hb := Janko4.LocalStructure.cover_cubic_residual_two_centralizer_bound
    q hq hthree x hx (P.subgroupOf Kg) (D.elementary.isPGroup.to_le inf_le_left).comap_subtype hi hPC
  rw [Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv] at hb
  exact (by omega : ¬ (16 : ℕ) ≤ 2) (hfix.trans hb)

/-- Every literal cover of L acting on the full exterior module is irreducible
on its ambient subgroups. The action and its quotient projection are unchanged. -/
theorem ExteriorMarking.cover_irreducible (a : ExteriorMarking D)
    {F : Subgroup G} (hVF : V ≤ F) (hFL : F ≤ L)
    (hcover : (L : Set G) ⊆ (F : Set G) * (L.pCoreIn 2 : Set G))
    (B : Subgroup G) (hBV : B ≤ V) (hFB : F ≤ normalizer (B : Set G)) :
    B = ⊥ ∨ B = V := by
  obtain ⟨⟨e,he⟩,_⟩ := a.cover_quotient hFL hcover
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ρ := (Representation.SL5TenDimensional.exteriorAction 2).comp π
  let : Representation.IsIrreducible ρ :=
    (Representation.irreducible_comp_surjective_iff π hπ _).mpr
      Representation.SL5ExteriorSquare.exteriorSquare_isIrreducible
  let d : Representation.BinaryConjugationSection F V ⊥ ρ := {
    section_le := hVF
    kernel_le := bot_le
    normalized := hFL.trans D.normalizes
    coordinates := a.coordinates.toMonoidHom
    onto := a.coordinates.surjective
    kernel_eq := by rw [(MonoidHom.ker_eq_bot_iff _).mpr a.coordinates.injective,bot_subgroupOf]
    equivariant := by
      intro f v
      have hh := congrArg Multiplicative.toAdd (a.equivariant (inclusion hFL f) v)
      change _ = Representation.SL5TenDimensional.exteriorAction 2 (π f) _
      rw [show π f = a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) (inclusion hFL f)) from he f]
      exact hh }
  by_cases hVB : V ≤ B
  · exact Or.inr (le_antisymm hBV hVB)
  · have hh := d.inf_eq_kernel_of_irreducible B hFB bot_le hVB
    rw [inf_eq_right.mpr hBV] at hh
    exact Or.inl hh


/-- In the actual exterior configuration, every binary subgroup normalized by
the intersection residual and centralizing V has zero r-commutator whenever
its r-commutators lie in V. A nonzero image would be all of V; coprime action
then supplies an actual cubic-fixed lift of a vector moved by the full residual,
contradicting that residual's proved normality in the full cubic centralizer.
The source R₁ and its nonzero commutator still have to be constructed. -/
theorem exterior_pushingUp_cubic_commutator_vanishes
    (s : SylowExteriorMarking D) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) (hn : K.Normal)
    (e : (K ⧸ center K) ≃* Janko4.Model) (k : K) (hk : orderOf k = 3)
    (hkF : ((k : H) : G) ∈ (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
    (hfix : 16 ≤ Nat.card (V ⊓ centralizer ({((k : H) : G)} : Set G) : Subgroup G))
    (r : G) (hr : orderOf r = 2)
    (hKC : K.map H.subtype ≤ centralizer ({r} : Set G))
    (hKN : ((K.map H.subtype).subgroupOf (centralizer ({r} : Set G))).Normal)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hVQ : V ≤ centralizer (Q : Set G))
    (hFQ : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype ≤ normalizer (Q : Set G))
    (hcomm : ∀ q ∈ Q, ⁅r,q⁆ ∈ V) : Q ≤ centralizer ({r} : Set G) := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let X := zpowers ((k : H) : G)
  have hc := hw.2.2.2.2.2.2.1
  have hVF := hw.2.2.2.2.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK : F ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hFr : F ≤ centralizer ({r} : Set G) := hFK.trans hKC
  have hXF : X ≤ F := zpowers_le.mpr hkF
  by_contra hQc
  obtain ⟨q,hq,hqr⟩ := SetLike.not_le_iff_exists.mp hQc
  have hne : ∃ q ∈ Q, ¬ Commute r q :=
    ⟨q,hq,fun hh => hqr (mem_centralizer_singleton_iff.mpr hh.symm)⟩
  have hsurj := centralCommutatorHom_surjective_of_irreducible Q V F hVQ r hcomm
    hFQ hFr (fun B hBV hFB => s.marking.cover_irreducible hVF hFL
      hw.2.2.2.2.2.2.2.1.subset B hBV hFB) hne
  have hcop : Nat.Coprime (Nat.card X) (Nat.card Q) := by
    obtain ⟨n,hn⟩ := hQ.exists_card_eq
    rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,hk,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let : Group.IsNilpotent Q := hQ.isNilpotent
  obtain ⟨v,hv,hvx,hvR⟩ := exterior_pushingUp_cubic_fixed_vector_moved s hw K hK e k hk hfix
  have hvX : v ∈ centralizer (X : Set G) := by
    simpa only [X,zpowers_eq_closure,centralizer_closure] using hvx
  obtain ⟨b,_,hb,hbcomm⟩ := centralCommutatorHom_exists_fixed_preimage
    Q V X hVQ r hcomm (hXF.trans hFQ) (hXF.trans hFr) inferInstance hcop hsurj v hv hvX
  have hbX : b ∈ centralizer ({((k : H) : G)} : Set G) := by
    simpa only [X,zpowers_eq_closure,centralizer_closure] using hb
  have hcent := exterior_pushingUp_cubic_residual_commutator_centralizes
    s h hw K hK hn e k hk hfix r hr hKC hKN
  exact hvR (hbcomm ▸ hcent (commutator_mem_commutator (mem_zpowers r) hbX))

/-- The unchanged exterior configuration with an actual moved fixed vector and
the obstruction to every binary central commutator image. -/
@[expose] def ExteriorPushingUpCommutatorCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ s.marking.M.subgroupOf H ∧
    1024 ≤ Nat.card W ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    Nonempty ((F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group) ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ s.marking.M).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      V ≤ K.map H.subtype ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (x : F) (k : K), ((k : H) : G) = (x : G) ∧ orderOf x = 3 ∧ orderOf k = 3 ∧
        16 ≤ Nat.card (V ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ∧
        let R := solvableResidual (centralizer ({k} : Set K))
        (IsQuasisimple R ∧ Nonempty ((R ⧸ center R) ≃* Sporadic.Mathieu.M22) ∧
          IsComponent (centralizer ({(k : H)} : Set H))
            (R.map (K.subtype.elementCentralizerMap k)) ∧
          R.IsCComponent ∧ IsM22Cover (R ⧸ pCore 2 R) ∧
          (R.map (K.subtype.elementCentralizerMap k)).Normal ∧
          (⟨k,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set K)) ∈ R ∧
          Nonempty ((R ⧸ solvableRadical R) ≃* Sporadic.Mathieu.M22) ∧
          ¬ R.map (H.subtype.comp (K.subtype.comp
            (centralizer ({k} : Set K)).subtype)) ≤ s.marking.M) ∧
        let I := F ⊔ J.pCoreIn 2
        I.pCoreIn 2 = J.pCoreIn 2 ∧ PushLE L J I ∧
          ∃ (r : G) (H' W' : Subgroup G),
            r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
            K.map H.subtype ⊔ J.pCoreIn 2 ≤ centralizer ({r} : Set G) ∧
            centralizer ({r} : Set G) ≤ H' ∧ Witness L V A I H' W' ∧
            IsComponentIn (K.map H.subtype) (centralizer ({r} : Set G)) ∧
            ((K.map H.subtype).subgroupOf (centralizer ({r} : Set G))).Normal ∧
            let Rg := R.map (H.subtype.comp (K.subtype.comp
              (centralizer ({k} : Set K)).subtype))
            let C := centralizer ({r} : Set G) ⊓ centralizer ({((k : H) : G)} : Set G)
            IsComponentIn Rg C ∧ (Rg.subgroupOf C).Normal ∧
            let X := centralizer ({((k : H) : G)} : Set G)
            IsComponentIn Rg X ∧ (Rg.subgroupOf X).Normal ∧
              ⁅zpowers r, X⁆ ≤ centralizer (Rg : Set G) ∧
              (∃ v ∈ V, v ∈ X ∧ v ∉ centralizer (Rg : Set G)) ∧
              ∀ Q : Subgroup G, IsPGroup 2 Q → V ≤ centralizer (Q : Set G) →
                F ≤ normalizer (Q : Set G) → (∀ q ∈ Q, ⁅r,q⁆ ∈ V) →
                Q ≤ centralizer ({r} : Set G)

/-- Carry the actual moved vector and the proved commutator obstruction
through the original exterior witnesses and their relative component placements. -/
theorem exterior_pushingUp_commutator_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpComponentEqualityCase s A) :
    ExteriorPushingUpCommutatorCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn,
    hRcX,hRnX,hcomm⟩ := hj
  have hfix' : 16 ≤ Nat.card (V ⊓ centralizer ({((k : H) : G)} : Set G) : Subgroup G) :=
    by simpa only [hkx] using hfix
  refine ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn,
    hRcX,hRnX,hcomm,exterior_pushingUp_cubic_fixed_vector_moved s hw K hK e k hk hfix',?_⟩
  intro Q hQ hVQ hFQ hcommQ
  exact exterior_pushingUp_cubic_commutator_vanishes s h hw K hK hn e k hk
    (by rw [hkx]; exact x.property) hfix' r ho hKc.1 hKn Q hQ hVQ hFQ hcommQ

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
