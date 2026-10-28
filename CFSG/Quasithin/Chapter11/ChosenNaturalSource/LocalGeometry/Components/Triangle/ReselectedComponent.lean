module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.OmegaCentralization
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ReselectedPoint
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstSporadic

/-!
# Relative-component recognition at the reselected point

The actual Cartan of a fixed-layer-free field-four natural module has a
cyclic subgroup of order three acting faithfully on its point. This follows
from the full scalar image on that point and the exponent-three Cartan torus.

A Sylow-normalized local PSL₃(4) group K centralizing this point lies in a
relatively normal C-component J of its normalizer. The exceptional
containing catalogue leaves only equality or the J₂, M₂₃ and J₄ quotient
models. The faithful cubic excludes all three strict rows. Thus K itself
is the unique containing component of the first residual, with normality
inside the actual point normalizer and inherited He membership.

ReselectedComponentSp4 applies this recognition to the literal common-Q
join and its previously constructed natural flag. No orientation is used.
Common-normal existence, the original SL₃(4) exclusion and both triangle
orientations remain with qt-d-1222-natural-relative-components; the
original earlier-source discharge remains with
qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith, 11.1.2, printed p.764, the assertion that K is
also the containing C-component for the reselected point.
-/

open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open Normalizers
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The original Cartan contains a faithful cubic actor on the actual point,
constructed from its full scalar image and its exponent-three torus. -/
theorem exists_faithful_cubic_on_point
    (hd : S.field.degree = 2) (hz : V ⊓ centralizer (L : Set G) = ⊥)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    {X : Subgroup G} (hX : IsCartan T L X) :
    ∃ A : Subgroup G, A ≤ X ∧ A ≤ normalizer (f.Vi 0 : Set G) ∧
      Nat.card A = 3 ∧ A ⊓ centralizer (f.Vi 0 : Set G) = ⊥ := by
  have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
  have hunit : Nat.card S.field.Carrierˣ = 3 := by rw [Nat.card_units,hF]
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 3
    (show 3 ∣ Nat.card S.field.Carrierˣ by rw [hunit])
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha
  have hscalar : lineScalars f hz a ≠ 1 := by
    intro he
    obtain ⟨v,hv,hv0⟩ := (Submodule.ne_bot_iff _).mp (f.space_ne_bot 0)
    let v' : f.space 0 := ⟨v,hv⟩
    have hv' : v' ≠ 0 := fun he => hv0 (congrArg Subtype.val he)
    have hh := lineScalars_apply f hz a ((lineCoordinates f hz).symm v')
    rw [he] at hh
    have hs : (a : S.field.Carrier) • v' = (1 : S.field.Carrier) • v' := by
      simpa using hh.symm
    exact ha1 (Units.ext ((smul_left_injective S.field.Carrier hv') hs))
  have himage : lineScalars f hz a ∈ lineImage f X := by
    rw [lineImage_eq_scalars f hX hfixed hz]
    exact MonoidHom.mem_range.mpr ⟨a,rfl⟩
  obtain ⟨x,hx,he⟩ := himage
  have hx3 : (x : G)^3 = 1 := by
    let e := c.cartanTorusEquiv hX
    have hunits (u : S.field.Carrierˣ) : u^3 = 1 := by
      rw [← hunit]
      exact pow_card_eq_one'
    have hpow : (⟨x,hx⟩ : X)^3 = 1 := by
      apply e.injective
      rw [map_pow,map_one]
      exact Prod.ext (hunits _) (hunits _)
    exact congrArg Subtype.val hpow
  have hx1 : (x : G) ≠ 1 := by
    intro hx1
    have hx' : x = 1 := Subtype.ext hx1
    exact hscalar (he.symm.trans (by rw [hx',map_one]))
  have horder : orderOf (x : G) = 3 := orderOf_eq_prime hx3 hx1
  let A := zpowers (x : G)
  have hAX : A ≤ X := zpowers_le.mpr hx
  have hAN : A ≤ normalizer (f.Vi 0 : Set G) := zpowers_le.mpr x.property
  have hcard : Nat.card A = 3 := (Nat.card_zpowers _).trans horder
  have hncentral : (x : G) ∉ centralizer (f.Vi 0 : Set G) := by
    intro hc
    have hk : x ∈ (lineAction f).ker := by rw [lineAction_ker]; exact hc
    exact hscalar (he.symm.trans hk)
  refine ⟨A,hAX,hAN,hcard,?_⟩
  let C := (centralizer (f.Vi 0 : Set G)).subgroupOf A
  have hC : C = ⊥ := by
    let : Fact (Nat.card A).Prime := ⟨hcard ▸ Nat.prime_three⟩
    rcases C.eq_bot_or_eq_top_of_prime_card with hb | ht
    · exact hb
    · exact (hncentral (show (⟨x,mem_zpowers _⟩ : A) ∈ C from ht ▸ mem_top _)).elim
  apply bot_unique
  rintro y ⟨hy,hc⟩
  have hy' : (⟨y,hy⟩ : A) ∈ C := hc
  exact congrArg Subtype.val (hC ▸ hy')

/-- A Sylow-normalized local PSL₃(4) group centralizing the natural point
is its relatively normal containing component. The exceptional strict
overcomponents are excluded by the actual Cartan scalar action. -/
theorem projective_four_relative_component_of_point_centralization
    (hd : S.field.degree = 2) (hz : V ⊓ centralizer (L : Set G) = ⊥)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    {X K : Subgroup G} (hX : IsCartan T L X)
    (hK : K ∈ Chapter1.L G T)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hmK : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hfirst : f.Li 0 ≤ K) (hpoint : K ≤ centralizer (f.Vi 0 : Set G)) :
    Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K ∧
      K ∈ Chapter1.He G ∧
      ∀ J : Subgroup G, Source.ComponentIn (normalizer (f.Vi 0 : Set G)) J →
        f.Li 0 ≤ J → J = K := by
  let H := normalizer (f.Vi 0 : Set G)
  have hKH : K ≤ H := hpoint.trans (Subgroup.centralizer_le_normalizer _)
  have hTH : (T : Subgroup G) ≤ H := f.invariant 0
  have hH := S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)
  have hSyl : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  obtain ⟨J,hJ,hKJ,_⟩ := exists_unique_normal_component hH hSyl hKH hK hTK
  have hlocalJ : J ∈ Chapter1.L G T := by
    refine ⟨hJ.1.2.subgroupOf_of_le le_sup_left (sup_le hJ.1.1 hTH),
      ⟨T.subtype le_sup_right,?_⟩,?_⟩
    · simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]
    · intro he
      apply f.V_ne_bot 0
      apply bot_unique
      have hUT : f.Vi 0 ≤ (T : Subgroup G) :=
        (D.centralQuotientPreimage_le _).trans D.le_sylow
      have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hUT)
        (hUT.trans (show (T : Subgroup G) ≤ J ⊔ (T : Subgroup G) from le_sup_right))
        (sup_le hJ.1.1 hTH)
      exact he ▸ hcore
  obtain ⟨f₀,hunique,_,hquot,_⟩ := exists_unique_marked_flag D S c
  have he : f.Li 0 = f₀.Li 0 := by
    change localResidual L (c.preimage (f.space 0)) = _
    rw [hunique 0 (f.space 0) (f.dimension 0) (f.invariant 0)]
    rfl
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree) := by
    rw [he]
    exact ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,hquot 0⟩
  obtain ⟨A,_,hAN,hcard,hfaith⟩ := exists_faithful_cubic_on_point D S f hd hz hfixed hX
  have hnot := first_component_not_cubic_sporadic D S f hm
    (hfirst.trans hpoint) hJ (hfirst.trans hKJ) hAN hcard hfaith
  have rule_out {B : Type} [Group B] [Finite B] (e : (J ⧸ pCore 2 J) ≃* B)
      (hb : center B = ⊥) (hr : 2 ≤ primeRank 3 B)
      (ho : IsPGroup 2 (MulAut.Outer B)) : False := by
    have hzJ : center (J ⧸ pCore 2 J) = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      intro z hzJ
      exact e.map_eq_one_iff.mp (hb.le ((centerCongr e) ⟨z,hzJ⟩).property)
    exact first_component_not_centerless_cubic D S f hm (hfirst.trans hpoint)
      hJ (hfirst.trans hKJ) hAN hcard hfaith hzJ
      ((primeRank_congr 3 e).symm ▸ hr) (ho.of_equiv (MulAut.outerCongr e).symm)
  have hsame : K = J := by
    rcases Chapter1.Section02.exceptional_local_overcomponent_models_or_jankoFour
      S.source.simpleQTKE T hK hTK hlocalJ hKJ (projective_four_exceptional_model hmK)
      with heq | hj2 | hm23 | hj4
    · exact heq
    · exact (rule_out hj2.some
        Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockGeometry.center_eq_bot
        Sporadic.LeechRelated.J2.three_rank_ge_two Sporadic.LeechRelated.J2.outer_isTwoGroup).elim
    · exact (hnot (FirstCubicSporadic.of_small_carrier (.inr (.inl hm23)))).elim
    · exact (rule_out hj4.some Janko4.model_center_eq_bot
        ChapterA.Section03.OddPrime.SourceModels.FourSporadic.j4_three_rank_ge_two
        Janko4.AdequateLocal.outer_isPGroup_two).elim
  have hnormal : Source.NormalComponentIn H K := hsame ▸ hJ
  obtain ⟨K',hK',hfirst',hHe,hunique'⟩ :=
    flag_exists_unique_normal_component_of_model D S f 0 hm
  have heq := hunique' K hnormal.1 hfirst
  exact ⟨hnormal,heq ▸ hHe,fun J hJ hfirstJ => (hunique' J hJ hfirstJ).trans heq.symm⟩


end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
