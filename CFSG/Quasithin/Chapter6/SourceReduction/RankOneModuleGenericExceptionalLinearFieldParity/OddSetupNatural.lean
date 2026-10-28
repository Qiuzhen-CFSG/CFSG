module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupQuotient
public import CFSG.Quasithin.Chapter3.Section02.SourceSelection
public import CFSG.Quasithin.Chapter6.Section02.NaturalSylowGeometry
public import CFSG.Quasithin.Chapter6.Section01.EscapeSize.Natural
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.SpecificGroups.SL2.OddFixedVectors
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The selected module and its local Sylow line in odd field degree

Odd degree eliminates the field action of T and gives
T = (T ∩ L) O₂(LT). The original Fundamental Setup exists, and its
central point is therefore precisely C_V(T ∩ L). For a natural module
this point has order 2ⁿ. A nonzero natural vector has a two-group
stabilizer in SL₂, so intersecting Sylow fixed lines coincide. Together
with irreducibility, this proves TI under N_G(L), including elements
that move the selected module to another copy.

Finally an odd nonidentity Cartan element has no nonzero natural fixed
vector. Coprime decomposition gives V = [V,A]. The natural marking
remains an explicit premise: constructing it and extending local TI
to all of G are still obligations of qt-d-1222-linear-field-parity.

Source: Aschbacher–Smith 5.1.17, printed pp.640–641, with 3.2.3
and 5.1.3 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- Odd field degree forces the literal inner-action Sylow factorization. -/
theorem sylow_factor_of_odd
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hodd : Odd n) :
    (T : Subgroup G) = (T : Subgroup G) ⊓ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hz : (cartanFieldAction hTL e).range = ⊥ := by
    by_contra hh
    exact (Nat.not_even_iff_odd.mpr hodd) (even_of_cartanFieldAction_ne_bot hTL e hF hh)
  have hi (t : T) : pCoreJoinAction 2 hTL (inclusion le_sup_right t) ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
    have ht : cartanFieldAction hTL e t = 1 := by
      have hm : cartanFieldAction hTL e t ∈ (cartanFieldAction hTL e).range := ⟨t,rfl⟩
      simpa only [hz, mem_bot] using hm
    have ht' : MulAut.congr e (pCoreJoinAction 2 hTL (inclusion le_sup_right t)) ∈
        Theory.PSL2.inner F := by
      rw [← Theory.PSL2.fieldProjection_ker]
      exact ht
    change MulAut.congr e (pCoreJoinAction 2 hTL (inclusion le_sup_right t)) ∈
      MulAut.innerSubgroup PSL(2,F) at ht'
    rw [← MulAut.map_innerSubgroup_congr e] at ht'
    obtain ⟨a,ha,he⟩ := ht'
    exact (MulAut.congr e).injective he ▸ ha
  have hc : center (L ⧸ pCore 2 L) = ⊥ := by
    apply (center _).eq_bot_iff_forall.mpr
    intro x hx
    apply e.injective
    rw [map_one]
    have hx' : e x ∈ center PSL(2,F) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
    simpa only [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] using hx'
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  have hPT : (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    rw [hP, subgroupOf_map_subtype]
  simpa only [hPT] using sup_core_factor_of_inner_action L (T : Subgroup G) hTL
    T.isPGroup' hc P (hPT.le.trans inf_le_left) hi

/-- Construct the Fundamental Setup from the original faithful local hypotheses. -/
theorem fundamental_exists (h : Input KnownSimple.IsKnownSimple T L W n) :
    Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L) := by
  have hmax : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop, ?_⟩
    intro K hK hLK
    exact le_antisymm (h.local_mem.1.2 hK hLK) hLK
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hc : 3 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ n by have := h.exponent; omega)
    omega
  have hqs := Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hc
    (e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm)
  have hOmega (Q : Subgroup G) : centralOmega Q = Stellmacher.omegaOneCenterAmbient Q := by
    apply le_antisymm
    · apply (omegaOneAmbient_le_iff _ _).mpr
      intro x hx hp
      exact (Stellmacher.mem_omegaOneCenterAmbient_iff Q x).mpr
        ⟨hx.1,hp,mem_centralizer_iff.mp hx.2⟩
    · intro x hx
      obtain ⟨hxQ,hp,hc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff Q x).mp hx
      exact (omegaOneAmbient_le_iff _ _).mp le_rfl x
        ⟨hxQ,mem_centralizer_iff.mpr hc⟩ hp
  have hm : ChapterA.Section04.intrinsicSignalizerModule L ≠ ⊥ := by
    have hh := h.local_mem.2.2.2.2
    rw [hOmega,commutator_comm] at hh
    simpa only [Subgroup.pCoreIn,ChapterA.Section04.intrinsicSignalizerModule,
      ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter] using hh
  exact Chapter3.Section02.source_exists_fundamentalSetup h.qtke T L hmax
    ⟨⟨h.local_mem.2.1,h.local_mem.2.2.1,h.local_mem.2.2.2.1⟩,hm⟩ hqs

/-- The original central point is exactly the selected module’s Sylow fixed space. -/
theorem fundamental_point_eq_sylow_fixed
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hodd : Odd n) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup =
      D.moduleSubgroup ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) := by
  have he : Chapter3.Section02.localJoin T L = L ⊔ (T : Subgroup G) :=
    componentOrbit_sup L T
  have hcore : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (D.moduleSubgroup : Set G) :=
    he ▸ D.core_centralizes_module
  have hf := sylow_factor_of_odd hTL hpsl hodd
  ext x
  constructor
  · intro hx
    refine ⟨hx.2, mem_centralizer_iff.mpr ?_⟩
    intro t ht
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx.1).2.2 t ht.1
  · intro hx
    refine ⟨(Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr ?_,hx.1⟩
    let := D.module_elementary
    refine ⟨D.module_le_sylow hx.1, elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx.1, ?_⟩
    have hc : (T : Subgroup G) ≤ centralizer ({x} : Set G) := by
      rw [hf]
      apply sup_le
      · intro t ht
        exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx.2 t ht)
      · intro t ht
        exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hcore ht) x hx.1).symm)
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hc ht)

/-- The selected natural point has the order of the defining field. -/
theorem fundamental_point_card
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup : Subgroup G) = 2 ^ n := by
  rw [fundamental_point_eq_sylow_fixed D hTL hpsl hodd]
  exact (hnat.sylow_intersection_geometry T hTL).1

/-- Natural modules have trivial intersection with distinct normalizer conjugates. -/
theorem natural_module_ti {V : Subgroup G} (hnat : IsNaturalModule L V n)
    {g : G} (hg : g ∈ normalizer (L : Set G)) :
    V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V := by
  have hnL : L ≤ normalizer (V : Set G) := by
    obtain ⟨F,_,_,_,_,hm⟩ := hnat
    exact hm.normalizes
  have hgL : L.map (MulAut.conj g).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp hg
  have hng : L ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hnL
    rwa [hgL, map_equiv_normalizer_eq] at hm
  rcases hnat.invariant_subgroup _ inf_le_left
      ((le_inf hnL hng).trans inf_normalizer_le_normalizer_inf) with he | he
  · exact Or.inl he
  · exact Or.inr (eq_of_le_of_card_ge (he.symm.le.trans inf_le_right)
      (by rw [card_map_of_injective (MulAut.conj g).injective])).symm

/-- Two Sylow fixed lines coincide whenever they share a nonidentity vector. -/
theorem natural_sylow_fixed_ti {V : Subgroup G} (hnat : IsNaturalModule L V n)
    (S R : Sylow 2 L) :
    (V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G)) ⊓
        (V ⊓ centralizer ((R : Subgroup L).map L.subtype : Set G)) = ⊥ ∨
      V ⊓ centralizer ((R : Subgroup L).map L.subtype : Set G) =
        V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
  classical
  by_cases hz : (V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G)) ⊓
      (V ⊓ centralizer ((R : Subgroup L).map L.subtype : Set G)) = ⊥
  · exact Or.inl hz
  right
  obtain ⟨x,hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hz
  have hx := x.property
  obtain ⟨F,_,_,_,_,e,f,hf⟩ := hnat
  let q : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hq
  let Q := R.mapSurjective hq
  have hfix (D : Subgroup L) (v : V) :
      (v : G) ∈ centralizer (D.map L.subtype : Set G) ↔
        ∀ a ∈ D.map q, a.val.mulVec (f v).toAdd = (f v).toAdd := by
    constructor
    · intro hv a ha
      obtain ⟨l,hl,rfl⟩ := ha
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      apply Subtype.ext
      have hh := hf l v
      change (f.symm (Multiplicative.ofAdd ((q l).val.mulVec (f v).toAdd)) : G) = _ at hh
      rw [hh]
      change (l : G) * (v : G) * (l : G)⁻¹ = (f.symm (f v) : G)
      rw [f.symm_apply_apply]
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hv _ (mem_map_of_mem _ hl))
    · intro hv
      apply mem_centralizer_iff.mpr
      rintro _ ⟨l,hl,rfl⟩
      have hh := hf l v
      change (f.symm (Multiplicative.ofAdd ((q l).val.mulVec (f v).toAdd)) : G) = _ at hh
      rw [hv _ (mem_map_of_mem q hl)] at hh
      change (f.symm (f v) : G) = _ at hh
      rw [f.symm_apply_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
  let v : V := ⟨x,hx.1.1⟩
  have hv : (f v).toAdd ≠ 0 := by
    intro he
    exact hx1 (Subtype.ext (congrArg (fun w : V => (w : G)) (f.injective (he.trans f.map_one.symm))))
  let C := MulAction.stabilizer SL(2,F) (f v).toAdd
  have hC : IsPGroup 2 C := Matrix.SL2.stabilizer_nonzero_isPGroup _ hv
  have hPC : (P : Subgroup SL(2,F)) ≤ C := by
    intro a ha
    exact (hfix S v).mp hx.1.2 a ha
  have hQC : (Q : Subgroup SL(2,F)) ≤ C := by
    intro a ha
    exact (hfix R v).mp hx.2.2 a ha
  have he : (Q : Subgroup SL(2,F)) = (P : Subgroup SL(2,F)) :=
    (Q.is_maximal' hC hQC).symm.trans (P.is_maximal' hC hPC)
  change (R : Subgroup L).map q = (S : Subgroup L).map q at he
  ext z
  constructor <;> intro hz
  · refine ⟨hz.1,(hfix S ⟨z,hz.1⟩).mpr ?_⟩
    have hh := (hfix R ⟨z,hz.1⟩).mp hz.2
    exact he ▸ hh
  · refine ⟨hz.1,(hfix R ⟨z,hz.1⟩).mpr ?_⟩
    have hh := (hfix S ⟨z,hz.1⟩).mp hz.2
    exact he.symm ▸ hh

/-- Local TI for the Sylow line, even when the conjugating element moves V. -/
theorem natural_point_ti_under_normalizer {V : Subgroup G}
    (hnat : IsNaturalModule L V n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {g : G} (hg : g ∈ normalizer (L : Set G)) :
    let Z := V ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G)
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      Z.map (MulAut.conj g).toMonoidHom = Z := by
  dsimp only
  rcases natural_module_ti hnat hg with hd | he
  · left
    exact bot_unique ((inf_le_inf inf_le_left (map_mono inf_le_left)).trans_eq hd)
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let a := L.normalizerMonoidHom ⟨g,hg⟩
  let R := S.mapSurjective a.surjective
  have hSmap : (S : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    rw [hS,subgroupOf_map_subtype]
  have hRmap : (R : Subgroup L).map L.subtype =
      ((T : Subgroup G) ⊓ L).map (MulAut.conj g).toMonoidHom := by
    change ((S : Subgroup L).map a.toMonoidHom).map L.subtype = _
    rw [map_map,show L.subtype.comp a.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp L.subtype from rfl,← map_map,hSmap]
  have hZ : (V ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G)).map
      (MulAut.conj g).toMonoidHom =
      V ⊓ centralizer ((R : Subgroup L).map L.subtype : Set G) := by
    rw [map_inf _ _ _ (MulAut.conj g).injective,he,hRmap]
    exact congrArg (fun X : Subgroup G => V ⊓ X)
      (Theory.Quasithin.map_centralizer (MulAut.conj g) ((T : Subgroup G) ⊓ L))
  rw [hZ]
  convert natural_sylow_fixed_ti hnat S R using 1 <;> rw [hSmap] <;> rfl

/-- Local TI for the literal point Ω₁Z(T) ∩ V of the Fundamental Setup. -/
theorem fundamental_point_ti_under_normalizer
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    {g : G} (hg : g ∈ normalizer (L : Set G)) :
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      Z.map (MulAut.conj g).toMonoidHom = Z := by
  dsimp only
  rw [fundamental_point_eq_sylow_fixed D hTL hpsl hodd]
  exact natural_point_ti_under_normalizer hnat hTL hg


/-- The actual nontrivial odd Cartan has no nonzero natural fixed vector. -/
theorem natural_cartan_fixed_eq_bot {V : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : 1 < n)
    (c : CartanPair T L H A B) (hnat : IsNaturalModule L V n) :
    V ⊓ centralizer (A : Set G) = ⊥ := by
  have ho : Odd (Nat.card A) := by
    have hh := OddHall.odd_hall_odd c.left_hall
    rwa [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv] at hh
  have hdis : Disjoint A (L.pCoreIn 2) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 L).exists_card_eq
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  have hA : A ≠ ⊥ := by
    intro he
    have hh := (c.left_cyclic_and_card hTL hpsl).2
    rw [he, Subgroup.card_bot] at hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ n by omega)
    omega
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have hAL : A ≤ L := c.left_le.trans inf_le_left
  obtain ⟨F,_,_,_,_,e,f,hf⟩ := hnat
  let q : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let l : L := ⟨a,hAL a.property⟩
  have hqne : q l ≠ 1 := by
    intro he
    have hl : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp he)
    have hg : (a : G) ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype hl
    exact ha (Subtype.ext (Subgroup.disjoint_def.mp hdis a.property hg))
  have hpow : q l ^ Nat.card A = 1 := by
    rw [← map_pow]
    have hlpow : l ^ Nat.card A = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : A => (z : G)) (pow_card_eq_one' (x := a))
    rw [hlpow,map_one]
  apply eq_bot_iff.mpr
  intro v hv
  have hfixed : (q l).val.mulVec (f ⟨v,hv.1⟩).toAdd = (f ⟨v,hv.1⟩).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    have hh := hf l ⟨v,hv.1⟩
    change (f.symm (Multiplicative.ofAdd ((q l).val.mulVec (f ⟨v,hv.1⟩).toAdd)) : G) = _ at hh
    rw [hh]
    change (a : G) * v * (a : G)⁻¹ = (f.symm (f ⟨v,hv.1⟩) : G)
    rw [f.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hv.2 a a.property)
  have hz := Matrix.SL2.odd_power_fixed_eq_zero (q l) (Nat.card A) ho hpow hqne _ hfixed
  exact mem_bot.mpr (congrArg (fun z : V => (z : G))
    (f.injective (hz.trans f.map_one.symm)))

/-- The actual Cartan moves the entire selected natural module. -/
theorem fundamental_cartan_commutator
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : 1 < n)
    (c : CartanPair T L H A B) (hnat : IsNaturalModule L D.moduleSubgroup n) :
    D.moduleSubgroup = ⁅D.moduleSubgroup,A⁆ := by
  let := D.module_elementary
  have hnorm : A ≤ normalizer (D.moduleSubgroup : Set G) := by
    obtain ⟨F,_,_,_,_,hm⟩ := hnat
    exact (c.left_le.trans inf_le_left).trans hm.normalizes
  have ho : Odd (Nat.card A) := by
    have hh := OddHall.odd_hall_odd c.left_hall
    rwa [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv] at hh
  have hcop : Nat.Coprime (Nat.card A) (Nat.card D.moduleSubgroup) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 D.moduleSubgroup).exists_card_eq
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  simpa only [natural_cartan_fixed_eq_bot hTL hpsl hn c hnat, sup_bot_eq] using
    eq_commutator_sup_centralizer_of_solvable_coprime D.moduleSubgroup A hnorm inferInstance hcop

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
