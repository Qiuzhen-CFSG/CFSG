module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionLinearNormalizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryTorus
public import Theory.SpecificGroups.PSL3.LinearThreeRadicalThirtyTwo
public import Theory.GroupTheory.PrimeCoreQuotientFixer
public import Theory.SpecificGroups.Janko4.PerfectCoverActions

/-!
# Excluding the degree-five J₄ row on the marked source action

The original coordinates construct an auxiliary torus Y≤K of order 31.
Coverage of the entire R₂, including its possible part outside K, puts its
original SL₃ image in the root plane. The F₃₂ matrix calculation and C_Q(Y)=1
then give C_R₂(Y)=1, hence [R₂,Y]=R₂ by coprime action. This is a proved
calculation for this degree; the scalar-cubic obstruction at degree two and
all legacy interfaces remain intact.

For a perfect central cover of J₄, faithful descent embeds its automorphism
group in J₄. Since 31 occurs only once in its order and in the secondary
PSL₂(32) quotient, a 31-element cannot act trivially on that quotient.
Thus Y has trivial image under the very same normalQuotientAction, forcing
the radical image to vanish, contrary to the source geometry. No full-Sylow
normalization or exhaustive proper-local catalogue is assumed.

The actual source torus stored in the witness is preserved; the auxiliary
Y is used only to exclude J₄. The final coordinate assembly consumes this
exclusion and retains the original full quotient and outer-torus clause.
Source: Aschbacher--Smith 4.3.10--16, printed pp.617--618. The J₄ carrier,
inner-automorphism theorem and order retain their imported attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {d : MSData c 5}

private theorem radical_projection_le (m : RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V) (s : SecondaryActionData c 5) :
    ((R₂ c).subgroupOf (K c)).map (linearThreeActor d.model) ≤
      (pointRadicalSL d.field.Carrier).map (pointLocalSL d.field.Carrier).subtype := by
  let A := (pointRadicalSL d.field.Carrier).map (pointLocalSL d.field.Carrier).subtype
  let J := A.comap (linearThreeActor d.model)
  have hbound : Q c ⊔ (secondary c).pCoreIn 2 ≤ J.map (K c).subtype := by
    apply sup_le
    · rw [s.core_eq_original]
      apply map_mono
      intro x hx
      change linearThreeActor d.model x ∈ A
      have hz : linearThreeActor d.model x = 1 := by
        change d.model (QuotientGroup.mk' _ x) = 1
        exact (congrArg d.model ((QuotientGroup.eq_one_iff x).mpr hx)).trans d.model.map_one
      rw [hz]
      exact one_mem A
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨⟨x,secondary_le_original x.property⟩,?_,rfl⟩
      have hh := (m.secondary_core_image (by decide)).le (mem_map_of_mem _ hx)
      rw [pointLocalSL_twoCore_eq] at hh
      exact mem_map_of_mem (pointLocalSL d.field.Carrier).subtype hh
  intro x hx
  obtain ⟨r,hr,rfl⟩ := hx
  have hh := ((m.radical_coverage (by decide) D s.core_eq).trans hbound) hr
  exact (mem_map_iff_mem (K c).subtype_injective).mp hh

private theorem original_torus_radical_fixed (m : RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V) (s : SecondaryActionData c 5)
    (Y : Subgroup G) (hcard : Nat.card Y = 31) (hYK : Y ≤ K c)
    (hYr : Y ≤ rootNormalizer c) (hfaith : Y ⊓ centralizer (root c : Set G) = ⊥)
    (hfix : Q c ⊓ centralizer (Y : Set G) = ⊥)
    (hsec : ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2) :
    R₂ c ⊓ centralizer (Y : Set G) = ⊥ := by
  have hF : Nat.card d.field.Carrier = 32 := by rw [d.field.card_eq,d.degree_eq]; rfl
  have hn : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  let := hn
  obtain ⟨y,hy⟩ := exists_ne (1 : Y)
  let k : K c := ⟨y,hYK y.property⟩
  let a := linearThreeActor d.model k
  have ha : a ∈ pointParabolicSL d.field.Carrier := m.actor_mem_pointParabolic k (hYr y.property)
  have hroot : a.val 0 0 ≠ 1 := by
    intro he
    have hk : (k : G) ∈ centralizer (root c : Set G) := by
      apply (m.centralizer_iff k).mpr
      obtain ⟨h10,h20⟩ := (mem_pointParabolicSL_iff _ _).mp ha
      exact (mem_pointLocalSL_iff _ _).mpr ⟨he,h10,h20⟩
    have hh : (y : G) ∈ Y ⊓ centralizer (root c : Set G) := ⟨y.property,hk⟩
    rw [hfaith,mem_bot] at hh
    exact hy (Subtype.ext hh)
  have hact : ∀ b ∈ pointLocalSL d.field.Carrier,
      ⁅a,b⁆ ∈ (pointRadicalSL d.field.Carrier).map (pointLocalSL d.field.Carrier).subtype := by
    intro b hb
    obtain ⟨z,hz⟩ := m.secondaryProjection_surjective (by decide) ⟨b,hb⟩
    have hc : ⁅(k : G),(z : G)⁆ ∈ (secondary c).pCoreIn 2 := by
      rw [commutator_comm] at hsec
      exact hsec (commutator_mem_commutator y.property z.property)
    obtain ⟨w,hw,hwe⟩ := hc
    have hwi := (m.secondary_core_image (by decide)).le (mem_map_of_mem _ hw)
    rw [pointLocalSL_twoCore_eq] at hwi
    refine ⟨m.secondaryProjection w,hwi,?_⟩
    change linearThreeActor d.model ⟨w,secondary_le_original w.property⟩ = ⁅a,b⁆
    have hwK : (⟨w,secondary_le_original w.property⟩ : K c) =
        ⁅k,⟨z,secondary_le_original z.property⟩⁆ := Subtype.ext hwe
    rw [hwK,map_commutatorElement]
    exact congrArg (fun v => ⁅a,v⁆) (congrArg Subtype.val hz)
  apply bot_unique
  intro r hr
  let rK : K c := ⟨r,m.radical_le_original (by decide) D s.core_eq hr.1⟩
  have hp := radical_projection_le m D s
    (mem_map_of_mem (linearThreeActor d.model) (show rK ∈ (R₂ c).subgroupOf (K c) from hr.1))
  obtain ⟨b,hb,hbe⟩ := hp
  change (b : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier) = linearThreeActor d.model rK at hbe
  have hab : a * (b : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier) = b * a := by
    rw [hbe]
    change linearThreeActor d.model k * linearThreeActor d.model rK =
      linearThreeActor d.model rK * linearThreeActor d.model k
    rw [←map_mul,←map_mul]
    apply congrArg (linearThreeActor d.model)
    exact Subtype.ext (mem_centralizer_iff.mp hr.2 y y.property)
  have hb1 := pointParabolic_radical_fixed_eq_one_thirtyTwo hF a ha hroot hact b hb hab
  have hrQ : r ∈ Q c := by
    rw [s.core_eq_original]
    refine ⟨rK,?_,rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    apply d.model.injective
    change linearThreeActor d.model rK = d.model 1
    rw [map_one,←hbe,hb1]
    rfl
  have hh : r ∈ Q c ⊓ centralizer (Y : Set G) := ⟨hrQ,hr.2⟩
  rwa [hfix] at hh

/-- At degree five the constructed source torus moves the actual whole radical.
This uses the marked root-plane calculation, not the legacy movement field. -/
theorem SecondaryActionData.exists_moving_radical_torus_five
    (s : SecondaryActionData c 5) (m : RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ∃ Y : Subgroup G, Nat.card Y=31 ∧ Y ≤ K c ∧ Y ≤ rootNormalizer c ∧
      ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2 ∧ ⁅R₂ c,Y⁆ = R₂ c := by
  obtain ⟨Y,_,hcard,hYK,hYr,hfaith,hfix,hsec,hRY,_⟩ :=
    m.exists_source_torus (by decide) D s.core_eq
  have hc : Nat.card Y=31 := hcard
  have hf := original_torus_radical_fixed m D s Y hc hYK hYr hfaith hfix hsec
  have hp : IsPGroup 2 (R₂ c) := isPGroup_pCoreIn 2 _
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card (R₂ c)) := by
    obtain ⟨j,hj⟩ := hp.exists_card_eq
    rw [hc,hj]
    exact (by decide : Nat.Coprime 31 2).pow_right j
  let : Group.IsNilpotent (R₂ c) := hp.isNilpotent
  have hh := eq_commutator_sup_centralizer_of_solvable_coprime (R₂ c) Y hRY inferInstance hcop
  exact ⟨Y,hc,hYK,hYr,hsec,by simpa only [hf,sup_bot_eq] using hh.symm⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Subgroup Theory.GroupTheory
open scoped commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

/-- A source torus of order 31 acts trivially on a perfect cover of J₄.
The rank-one quotient, not the entire secondary subgroup, is centralized. -/
theorem SecondaryActionData.janko_four_torus_action_eq_bot
    (s : SecondaryActionData c 5)
    (e : SecondaryActionData.componentImage s ≃* Janko4.Model)
    (Y : Subgroup G) (hYr : Y ≤ rootNormalizer c) (hcard : Nat.card Y=31)
    (hsec : ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2) :
    SecondaryActionData.image s Y = ⊥ := by
  let := s.normal
  let := s.quasisimple
  let A := s.component ⧸ pCore 2 s.component
  let X := SecondaryActionData.secondaryImage s
  let q := (SecondaryActionData.sieveCentralQuotientEquiv s).trans e
  let f : MulAut A →* Janko4.Model :=
    Janko4.modelConjEquiv.symm.toMonoidHom.comp (MulAut.centralQuotientAction q)
  have hfi : Function.Injective f :=
    Janko4.modelConjEquiv.symm.injective.comp (MulAut.centralQuotientAction_injective q)
  have hsq : ¬ 31^2 ∣ Nat.card (MulAut A) := by
    intro hh
    have hd := hh.trans (card_dvd_of_injective f hfi)
    rw [Janko4.Cardinality.model_card] at hd
    norm_num at hd
  have hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^5) :=
    SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hd : 31 ∣ Nat.card X := by
    have hh := card_quotient_dvd_card (pCore 2 X)
    rw [Nat.card_congr (a.trans (Theory.PSL2.sl2QuotientEquiv F).symm).toEquiv,
      Atlas.card_sl_two,hF] at hh
    exact (by decide : 31 ∣ 2^5*((2^5)^2-1)).trans hh
  have hz : center (X ⧸ pCore 2 X)=⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hh : a x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
      apply mem_center_iff.mpr
      intro z
      obtain ⟨y,rfl⟩ := a.surjective z
      simpa only [map_mul] using congrArg a (mem_center_iff.mp hx y)
    rw [GorensteinWalter.psl2_center_eq_bot,mem_bot] at hh
    exact a.injective (hh.trans a.map_one.symm)
  have hcomm : ⁅X,SecondaryActionData.image s Y⁆ ≤ X.pCoreIn 2 := by
    change ⁅SourceImages.image c s.component (secondary c),SourceImages.image c s.component Y⁆ ≤ X.pCoreIn 2
    rw [←SourceImages.image_commutator c s.component _ _
      (s.secondary_le.trans (map_subtype_le _)) hYr]
    exact (map_mono (subgroupOf_mono _ hsec)).trans (SourceImages.secondary_core_le c s.component)
  have hnY : SecondaryActionData.image s Y ≤ normalizer (X : Set (MulAut A)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact hcomm.trans (pCoreIn_le 2 X)
  by_contra hne
  obtain ⟨p,hp,_,hpdiv,y,hy,ho⟩ := SourceImages.torus_prime_action_of_nontrivial_image
    c s.component (n:=5) (by decide) Y hYr hcard hne
  have hp31 : p=31 := (Nat.dvd_prime (by decide : Nat.Prime 31)).mp hpdiv |>.resolve_left hp.ne_one
  rcases hp31 with rfl
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  have hyi : s.action y ∈ SecondaryActionData.image s Y := mem_map_of_mem _ hy
  apply prime_order_not_trivial_on_twoCore_quotient X hz (by decide : Nat.Coprime 2 31)
    hd hsq (s.action y) (hnY hyi) ?_ ho
  intro b hb
  rw [commutator_comm] at hcomm
  exact hcomm (commutator_mem_commutator hyi hb)

/-- The marked degree-five root plane excludes J₄ on the literal source action. -/
theorem SecondaryActionData.not_janko_four_inner_of_coordinates
    (s : SecondaryActionData c 5) (d : MSData c 5) (m : RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V)
    (e : SecondaryActionData.componentImage s ≃* Janko4.Model) : False := by
  obtain ⟨Y,hcard,_,hYr,hsec,hm⟩ :=
    SecondaryActionData.exists_moving_radical_torus_five s m D
  have hz := SecondaryActionData.janko_four_torus_action_eq_bot s e Y hYr hcard hsec
  let := s.normal
  apply s.radical_action
  have hh := SourceImages.image_commutator c s.component (R₂ c) Y s.radical_le hYr
  change SourceImages.image c s.component Y = ⊥ at hz
  rw [hm,hz,commutator_bot_right] at hh
  exact hh
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
