module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSClassification
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSMarking
public import Theory.Representation.SL3.ParabolicSubgroups

/-!
# The full source module inside the natural center

In the constrained source configuration the original full module W lies
properly in U=Z(Q): W centralizes the radical containing Q, and equality
would force H into N_G(L). A natural-center marking then excludes the
point-parabolic orientation. In the line orientation, additive-subgroup
transvections identify [U,L] with W, without assuming scalar closure of W.

The checked initial omega splitting and the absence of L-fixed vectors in U
give C_S(K)=1 using the same natural-center marking. The final constructor
combines these facts with the original natural/dual sections and the Sylow
radical inequalities to produce MSData with simultaneous original markings.
NonblockMSConstruction removes its parabolic premise and applies the result
to the original secondary component.

Whole-core classification retains qt-c134-nonbinary-linear-three-source;
its final discharge and strict secondary-core enlargement remain with the
nonblock assembly owner. Source: Aschbacher--Smith C.1.34(3), pp.136--137,
and original 4.3.8--10, pp.616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

omit [Finite G] in
private theorem fullModule_moved : ⁅W c,L⁆ = W c := by
  have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  exact (show W c = ⁅W c,L⁆ from by simpa only [hs] using c.c28.module_commutator).symm

theorem fullModule_le_coreCenter (hf : generalizedFitting c.K = pCore 2 c.K) :
    W c ≤ U c := by
  have hWQ := (fullModule_lt_core c hf).le
  have hQR : Q c ≤ c.I.pCoreIn 2 := by
    rw [core_eq_blockLayer]
    exact (map_mono (map_mono (ChapterC.blockU_le_core (L := c.K)))).trans
      ((map_mono (pCoreIn_le_of_subnormal 2 c.component.subnormal)).trans
        c.c28.ambient_core_le_radical)
  intro w hw
  refine ⟨⟨w,hWQ hw⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro q
  obtain ⟨z,hz,hzw⟩ := c.c28.module_le_center_radical hw
  apply Subtype.ext
  have hh := congrArg (fun x : c.I.pCoreIn 2 => (x : G))
    (mem_center_iff.mp hz ⟨q,hQR q.property⟩)
  have hzw' : (z : G) = w := hzw
  simpa only [Subgroup.coe_mul,hzw'] using hh

omit [Finite G] in
private theorem center_normalized : c.H ≤ normalizer (U c : Set G) :=
  (core_normalized c).trans (normalizer_le_normalizer_characteristic_image (Q c) (center (Q c)))

theorem fullModule_lt_coreCenter (hf : generalizedFitting c.K = pCore 2 c.K) :
    W c < U c := by
  apply lt_of_le_of_ne (fullModule_le_coreCenter hf)
  intro he
  have hh : c.H ≤ normalizer (W c : Set G) := he ▸ center_normalized
  exact c.outside (((le_inf le_rfl hh).trans c.c28.module_normalizer).trans inf_le_right)

omit [Finite G] in
private theorem natural_coordinates {F : Type*} [Field F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3)) :
    ∃ f : U c ≃* Multiplicative (Fin 3 → F),
      ∀ (k : K c) (u v : U c), (v : G) = k * (u : G) * (k : G)⁻¹ →
        (f v).toAdd = (linearThreeActor e k).val.mulVec (f u).toAdd := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,f,hf⟩ := hm
  let := hn
  exact ⟨QuotientGroup.quotientBot.symm.trans f,hf⟩

section Coordinates
variable {F : Type*} [Field F]
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (f : U c ≃* Multiplicative (Fin 3 → F))
  (he : ∀ (k : K c) (u v : U c), (v : G) = k * (u : G) * (k : G)⁻¹ →
    (f v).toAdd = (linearThreeActor e k).val.mulVec (f u).toAdd)

private abbrev sourceImage : Subgroup (Multiplicative (Fin 3 → F)) :=
  ((W c).subgroupOf (U c)).map f.toMonoidHom
private abbrev localImage : Subgroup SL(3,F) := (L.subgroupOf (K c)).map (linearThreeActor e)

include hf in
private theorem sourceImage_ne_bot : (sourceImage f).toAddSubgroup' ≠ ⊥ := by
  intro hz
  apply c.c28.module_nontrivial
  apply bot_unique
  intro w hw
  let u : U c := ⟨w,fullModule_le_coreCenter hf hw⟩
  have hh : (f u).toAdd ∈ (sourceImage f).toAddSubgroup' := ⟨u,hw,rfl⟩
  rw [hz] at hh
  have hu : u = 1 := f.map_eq_one_iff.mp (Multiplicative.toAdd.injective hh)
  exact mem_bot.mpr (congrArg Subtype.val hu)

include he in
omit [Finite G] in
private theorem sourceImage_invariant :
    ∀ g ∈ localImage e, ∀ v ∈ (sourceImage f).toAddSubgroup',
      g.val.mulVec v ∈ (sourceImage f).toAddSubgroup' := by
  rintro g ⟨k,hk,rfl⟩ v ⟨u,hu,rfl⟩
  let w : U c := (U c).normalizerMonoidHom
    ⟨k,center_normalized ((map_subtype_le _) k.property)⟩ u
  have hw : (w : G) = k * (u : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
  refine ⟨w,?_,?_⟩
  · change (w : G) ∈ W c
    rw [hw]
    have hn : L ≤ normalizer (W c : Set G) := by
      apply le_normalizer_iff_commutator_le_right.mpr
      rw [commutator_comm,fullModule_moved]
    exact (mem_normalizer_iff.mp (hn hk) u).mp hu
  · exact Multiplicative.toAdd.injective (he k u w hw)

include hf he in
private theorem sourceImage_moved :
    ∀ A : AddSubgroup (Fin 3 → F),
      (∀ g ∈ localImage e, ∀ v ∈ (sourceImage f).toAddSubgroup', g.val.mulVec v - v ∈ A) →
      (sourceImage f).toAddSubgroup' ≤ A := by
  intro A hA
  let B := (A.toSubgroup.comap f.toMonoidHom).map (U c).subtype
  have hc : ⁅L,W c⁆ ≤ B := by
    apply commutator_le.mpr
    intro l hl w hw
    let k : K c := ⟨l,c.le_component hl⟩
    let u : U c := ⟨w,fullModule_le_coreCenter hf hw⟩
    let v : U c := (U c).normalizerMonoidHom
      ⟨k,center_normalized ((map_subtype_le _) k.property)⟩ u
    have hv : (v : G) = k * (u : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    refine ⟨v * u⁻¹,?_,?_⟩
    · change (f (v * u⁻¹)).toAdd ∈ A
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,he k u v hv,←sub_eq_add_neg]
      exact hA _ (mem_map_of_mem _ hl) _ ⟨u,hw,rfl⟩
    · rfl
  rw [commutator_comm,fullModule_moved] at hc
  rintro a ⟨u,hu,rfl⟩
  obtain ⟨v,hv,hvu⟩ := hc hu
  have hvu : v = u := Subtype.ext hvu
  subst v
  exact hv

include hf in
private theorem sourceImage_ne_top : (sourceImage f).toAddSubgroup' ≠ ⊤ := by
  intro ht
  apply (fullModule_lt_coreCenter hf).not_ge
  intro u hu
  have hh : (f ⟨u,hu⟩).toAdd ∈ (sourceImage f).toAddSubgroup' := ht ▸ trivial
  obtain ⟨v,hv,hvu⟩ := hh
  have hvu : v = ⟨u,hu⟩ := f.injective hvu
  change (v : G) ∈ W c at hv
  simpa only [hvu] using hv

include hf he in
private theorem source_line_of_parabolic
    (hp : localImage e = pointLocalSL F ∨ localImage e = lineLocalSL F) :
    localImage e = lineLocalSL F := by
  rcases hp with hp | hp
  · exfalso
    exact sourceImage_ne_top hf f
      (Representation.SL3ParabolicNatural.point_eq_top_of_moved _ (sourceImage_ne_bot hf f)
        (hp ▸ sourceImage_invariant e f he) (hp ▸ sourceImage_moved e hf f he))
  · exact hp

include hf he in
private theorem source_commutator_of_parabolic
    (hp : localImage e = pointLocalSL F ∨ localImage e = lineLocalSL F) :
    ⁅U c,L⁆ = W c := by
  apply le_antisymm
  · rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl u hu
    let k : K c := ⟨l,c.le_component hl⟩
    let x : U c := ⟨u,hu⟩
    let y : U c := (U c).normalizerMonoidHom
      ⟨k,center_normalized ((map_subtype_le _) k.property)⟩ x
    have hy : (y : G) = k * (x : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    have hd : (f (y*x⁻¹)).toAdd ∈ (sourceImage f).toAddSubgroup' := by
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,he k x y hy,←sub_eq_add_neg]
      exact Representation.SL3ParabolicNatural.displacement_mem_of_moved _ hp _
        (sourceImage_ne_bot hf f) (sourceImage_invariant e f he)
        (sourceImage_moved e hf f he) _ (mem_map_of_mem _ hl) _
    obtain ⟨z,hz,hzy⟩ := hd
    have hzy : z = y*x⁻¹ := f.injective hzy
    have hz' : ((y*x⁻¹ : U c) : G) ∈ W c := hzy ▸ hz
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,hy,commutatorElement_def] using hz'
  · rw [←fullModule_moved (c := c)]
    exact commutator_mono (fullModule_le_coreCenter hf) le_rfl
end Coordinates

theorem natural_center_line_and_fullModule {F : Type*} [Field F]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hp : (L.subgroupOf (K c)).map (linearThreeActor e) = pointLocalSL F ∨
      (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F ∧ ⁅U c,L⁆ = W c := by
  obtain ⟨f,hf'⟩ := natural_coordinates e hm
  exact ⟨source_line_of_parabolic e hf f hf' hp,source_commutator_of_parabolic e hf f hf' hp⟩

omit [Finite G] in
private theorem natural_center_fixed_eq_bot {F : Type*} [Field F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    U c ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨f,hf⟩ := natural_coordinates e hm
  apply bot_unique
  intro u hu
  have hz : (f ⟨u,hu.1⟩).toAdd = 0 := by
    apply Representation.SL3ParabolicNatural.line_fixed_zero
    intro g hg
    obtain ⟨k,hk,rfl⟩ := hL.ge hg
    have hh := hf k ⟨u,hu.1⟩ ⟨u,hu.1⟩ (by
      have hc := mem_centralizer_iff.mp hu.2 k hk
      simp only [hc,mul_assoc,mul_inv_cancel,mul_one])
    exact hh.symm
  exact mem_bot.mpr (congrArg Subtype.val
    (f.map_eq_one_iff.mp (Multiplicative.toAdd.injective hz)))

/-- The natural whole center gives the source Sylow-centralizer conclusion.
The already proved initial omega splitting is used with its original subgroups;
its potentially different quotient marking is immaterial to this argument. -/
theorem natural_center_sylow_centralizer {F : Type} [Field F] [Finite F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    S c ⊓ centralizer (K c : Set G) = ⊥ := by
  obtain ⟨hs,_⟩ := ms_initial_omega_split c D hf n hn hF e
  have hfix := natural_center_fixed_eq_bot e hm hL
  let A := movedCoreOmega c
  let C := coreOmega c ⊓ centralizer (K c : Set G)
  have hAU : A ≤ U c := ms_initialMoved_le_center c
  have hAK : A ≤ K c := hAU.trans ((map_subtype_le _).trans
    ((Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 _) le_rfl)))
  have hAC : A ≤ normalizer (C : Set G) :=
    ((le_centralizer_iff.mpr (inf_le_right.trans (centralizer_le hAK)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have he : coreOmega c ⊓ centralizer (L : Set G) = C := by
    apply le_antisymm
    · intro z hz
      have hz' : z ∈ (A : Set G) * (C : Set G) := by
        rw [←coe_mul_of_left_le_normalizer_right A C hAC]
        exact hs.ge hz.1
      obtain ⟨a,ha,b,hb,hab⟩ := hz'
      have hbL : b ∈ centralizer (L : Set G) := centralizer_le c.le_component hb.2
      have haL : a ∈ centralizer (L : Set G) := by
        have hh := (centralizer (L : Set G)).mul_mem hz.2
          ((centralizer (L : Set G)).inv_mem hbL)
        rw [←hab,mul_assoc,mul_inv_cancel,mul_one] at hh
        exact hh
      have ha1 : a = 1 := mem_bot.mp (hfix.le ⟨hAU ha,haL⟩)
      have hbz : b = z := by simpa only [ha1,one_mul] using hab
      exact hbz ▸ hb
    · exact inf_le_inf_left _ (centralizer_le c.le_component)
  apply c.nonblock_sylow_centralizer_eq_bot
  apply le_antisymm
  · intro z hz
    exact ⟨hz.1,(he.le ⟨c.nonblock_omega_sylow_le_core_omega hf hz.1,hz.2⟩).2⟩
  · exact inf_le_inf_left _ (centralizer_le c.le_component)

/-- Construct the original MS witness with both markings from the genuine
third-case section models and radical inequalities. The full module,
Sylow centralizer, line orientation and simultaneous Sylow placement are derived.
The whole-core classification and un-oriented parabolic recognition remain
explicit earlier source obligations of this task and its existing producer. -/
theorem exists_msData_of_natural_center_sections
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (hnat : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F.Carrier) 3))
    (hdual : HasSectionModel (K c) (Q c) (U c) (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F.Carrier) 3).dual.prod
        (Representation.specialLinearNatural (k := F.Carrier) 3).dual))
    (hpar : (L.subgroupOf (K c)).map (linearThreeActor e) = pointLocalSL F.Carrier ∨
      (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F.Carrier)
    (hrad : ∀ P : Sylow 2 (K c ⊔ c.I.pCoreIn 2 : Subgroup G),
      c.I.pCoreIn 2 ≤ (P : Subgroup (K c ⊔ c.I.pCoreIn 2 : Subgroup G)).map
        (K c ⊔ c.I.pCoreIn 2 : Subgroup G).subtype →
      MSNotCentralizerCore (K c) (c.I.pCoreIn 2)
        ((P : Subgroup (K c ⊔ c.I.pCoreIn 2 : Subgroup G)).map
          (K c ⊔ c.I.pCoreIn 2 : Subgroup G).subtype)) :
    ∃ d : MSData c n, d.field = F ∧
      (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier := by
  have hF : Nat.card F.Carrier = 2^n := F.card_eq.trans (congrArg (2^·) hdegree)
  obtain ⟨hL,hW⟩ := natural_center_line_and_fullModule hf e hnat hpar
  let d : MSData c n := {
    field := F
    degree_eq := hdegree
    model := e
    pair := msPair_of_quotient c D hf n (by omega) hF e
    commutator_eq := ms_commutator_eq c
    natural := hnat
    doubleDual := hdual
    radical_not_centralizer_core := hrad
    fullModule := hW
    centralizer := natural_center_sylow_centralizer D hf n hn hF e hnat hL }
  obtain ⟨g,hL',hSL'⟩ := d.exists_simultaneous_marking D hL
  exact ⟨d.conjugateModel g.val,rfl,hL',hSL'⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
