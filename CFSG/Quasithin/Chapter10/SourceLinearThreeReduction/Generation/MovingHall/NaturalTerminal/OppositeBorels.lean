module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.BothBlocks
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.OddSylowCentralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import Theory.GroupTheory.ConjugateOrbitIndexTwoStabilizer
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.TorusSource.Axes
/-!
# The opposite Borel of the selected general-field block

The two commuting original blocks place the opposite Hall axis in the
centralizer of the selected comparison Sylow. Odd self-centralizing action
therefore makes that axis centralize the comparison block. The common
Baumann group normalizes the block, so its commutator with the opposite
axis also centralizes it. The prescribed original exchanger carries the
common Sylow into this centralizer; trivial center forces the conjugate
block to be distinct. Block commutation supplies the commuting comparison
pair, with the original Hall intersection and both quotient markings intact.

The exported source application constructs this geometry from natural
marking and original Borel placement. The same assembly owner retains the
terminal overcomponent and the discharge of those two earlier premises.
Source: Aschbacher–Smith 10.2.3(4), printed p.747.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterC
open ChapterB.QuasisimpleSource ChapterC.GlaubermanNiles
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem center_eq_bot_map {X : Type*} [Group X]
    (K : Subgroup X) (f : X →* G) (hf : Function.Injective f) (hz : center K = ⊥) :
    center (K.map f) = ⊥ := by
  let a := K.equivMapOfInjective f hf
  apply bot_unique
  intro k hk
  have hh := (centerCongr a.symm ⟨k,hk⟩).property
  change a.symm k ∈ center K at hh
  rw [hz,mem_bot] at hh
  exact mem_bot.mpr (a.symm.injective (hh.trans a.symm.map_one.symm))

private theorem conjugate_ne_of_sylow_centralized (K P : Subgroup G)
    (hK : IsShort K) (hz : center K = ⊥) (hP : Chapter1.IsSylowIn 2 P K)
    (t : G) (hc : P.map (MulAut.conj t).toMonoidHom ≤ centralizer (K : Set G)) :
    K.map (MulAut.conj t).toMonoidHom ≠ K := by
  intro he
  have hQ := Chapter1.Section02.IndexTwo.isSylowIn_map hP (MulAut.conj t).toMonoidHom
  rw [he] at hQ
  apply hK.ambient_sylow_ne_bot K _ hQ
  apply bot_unique
  intro x hx
  have hxK := (Chapter1.isSylowIn_iff.mp hQ).2.1 hx
  have hxc : (⟨x,hxK⟩ : K) ∈ center K := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hc hx y y.property)
  rw [hz,mem_bot] at hxc
  exact mem_bot.mpr (congrArg K.subtype hxc)

variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]

/-- The prescribed conjugate has the literal general-field Hall commutator Sylow. -/
theorem Context.original_conjugate_axis_sylow
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    {t : G} (ht : t ∈ (T : Subgroup G))
    (A : Subgroup G) (hAL : A ≤ L.map (MulAut.conj t).toMonoidHom)
    (hAB : A ≤ B.map H.subtype) (hne : A ≠ ⊥) :
    ⁅baumann (T : Subgroup G),A⁆ = baumann (T : Subgroup G) ⊓ L.map (MulAut.conj t).toMonoidHom ∧
      Chapter1.IsSylowIn 2 ⁅baumann (T : Subgroup G),A⁆ (L.map (MulAut.conj t).toMonoidHom) := by
  let S := baumann (T : Subgroup G)
  let f := MulAut.conj t
  let J := L.map f.toMonoidHom
  let a : L ≃* J := f.subgroupMap L
  have hBR := hBB.trans ((map_subtype_le _).trans inf_le_left)
  obtain ⟨hnat,hcore,_⟩ := ctx.original_natural_block_core D n hn hF e mark hBR hb
  have hJ : IsL2EvenBlock J n := hnat.of_mulEquiv a
  have hcJ : pCore 2 J = blockU J := by
    rw [←pCore_map_iso 2 a,hcore,blockU,map_commutator,pCore_map_iso,
      map_top_of_surjective _ a.surjective,blockU]
  have hSm : S.map f.toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_baumann _ ((T : Subgroup G).le_normalizer ht))
  have hSL := ctx.baumann_normalizes_original D n hn hF e
  have hSJ : S ≤ normalizer (J : Set G) := by
    have h := map_mono (f := f.toMonoidHom) hSL
    rwa [hSm,map_equiv_normalizer_eq] at h
  have hSP : Chapter1.IsSylowIn 2 (S ⊓ L) L := by
    let X := localOrbit T L ⊔ S
    have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
    have hXM : X ≤ D.maximalLocal := sup_le (localOrbit T L).le_normalizer
      (inf_le_left.trans (le_normalizer_componentOrbit L T))
    exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      (ctx.original_baumann_sylow D n hn hF e) hLX
      (D.component_in_maximalLocal.subgroupOf_of_le hLX hXM).subnormal
  have hSQ : Chapter1.IsSylowIn 2 (S ⊓ J) J := by
    have h := Chapter1.Section02.IndexTwo.isSylowIn_map hSP f.toMonoidHom
    rwa [map_inf _ _ _ f.injective,hSm] at h
  exact hJ.ambient_odd_commutator_sylow J S A hcJ hSQ hAL
    (ctx.odd_card_of_le_hall_image A hAB) hne
    (hAB.trans (ctx.original_block_hall_normalizes_baumann D n hn hF e mark hBB hb)) hSJ

/-- Both axis orientations construct the opposite Borel centralizer and distinct commuting comparison pair. -/
theorem Context.aligned_opposite_borel_centralizes
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (hbL : IsBlock (L.subgroupOf (localJoin T L)))
    (K : Subgroup H) (hbK : IsBlock K) (hzK : center K = ⊥)
    (hSK : baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) ≤ normalizer (K : Set H))
    (hBK : B ≤ normalizer (K : Set H))
    (hP : Chapter1.IsSylowIn 2 ⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆ (K.map H.subtype))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (A₁ A₂ : Subgroup G) (hA₁L : A₁ ≤ L)
    (hA₂L : A₂ ≤ L.map (MulAut.conj t).toMonoidHom)
    (hA₁B : A₁ ≤ B.map H.subtype) (hA₂B : A₂ ≤ B.map H.subtype)
    (hA₁ne : A₁ ≠ ⊥) (hA₂ne : A₂ ≠ ⊥)
    (ha : (B ⊓ K).map H.subtype = A₁ ∨ (B ⊓ K).map H.subtype = A₂) :
    (let S := baumann (T : Subgroup G)
     ((B ⊓ K).map H.subtype = A₁ ∧
       (⁅S,A₂⁆ ⊔ A₂ : Subgroup G) ≤ centralizer (K.map H.subtype : Set G)) ∨
     ((B ⊓ K).map H.subtype = A₂ ∧
       (⁅S,A₁⁆ ⊔ A₁ : Subgroup G) ≤ centralizer (K.map H.subtype : Set G))) ∧
      (K.map H.subtype).map (MulAut.conj t).toMonoidHom ≠ K.map H.subtype ∧
      K.map H.subtype ≤ centralizer ((K.map H.subtype).map (MulAut.conj t).toMonoidHom : Set G) := by
  let S := baumann (T : Subgroup G)
  let J := L.map (MulAut.conj t).toMonoidHom
  let K₀ := K.map H.subtype
  let P := ⁅S,(B ⊓ K).map H.subtype⁆
  have hk : IsShort K₀ := hbK.short.of_mulEquiv (K.equivMapOfInjective H.subtype H.subtype_injective)
  have hzk : center K₀ = ⊥ := center_eq_bot_map K H.subtype H.subtype_injective hzK
  have hBm : (baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H)).map H.subtype = S := by
    have h := baumann_map_injective H.subtype H.subtype_injective
      (T.subtype ctx.hstar.1.1.2 : Subgroup H)
    change (baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H)).map H.subtype =
      baumann ((T.subtype ctx.hstar.1.1.2 : Subgroup H).map H.subtype) at h
    exact h.trans (congrArg baumann (map_subgroupOf_eq_of_le ctx.hstar.1.1.2))
  have hSK₀ : S ≤ normalizer (K₀ : Set G) := by
    have h := (map_mono (f := H.subtype) hSK).trans (K.le_normalizer_map H.subtype)
    rwa [hBm] at h
  have hBK₀ : B.map H.subtype ≤ normalizer (K₀ : Set G) :=
    (map_mono hBK).trans (K.le_normalizer_map H.subtype)
  have hcomm : L ≤ centralizer (J : Set G) := source_original_block_commutes_prescribed_conjugate D hbL ht htn
  obtain ⟨hS₁,_⟩ := ctx.original_block_axis_borel D n hn hF e mark hBB hbL A₁ hA₁L hA₁B hA₁ne
  obtain ⟨hS₂,_⟩ := ctx.original_conjugate_axis_sylow D n hn hF e mark hBB hbL ht A₂ hA₂L hA₂B hA₂ne
  have hSm : S.map (MulAut.conj t).toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_baumann _ ((T : Subgroup G).le_normalizer ht))
  have hswap : J.map (MulAut.conj t).toMonoidHom = L :=
    conjugate_twice_eq_of_index_two L (T : Subgroup G) (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 ctx.nonnormal) inf_le_right ht
  have hresult : ((B ⊓ K).map H.subtype = A₁ ∧
       (⁅S,A₂⁆ ⊔ A₂ : Subgroup G) ≤ centralizer (K₀ : Set G)) ∨
     ((B ⊓ K).map H.subtype = A₂ ∧
       (⁅S,A₁⁆ ⊔ A₁ : Subgroup G) ≤ centralizer (K₀ : Set G)) := by
    rcases ha with ha | ha
    · have hPL : P ≤ L := by change ⁅S,_⁆ ≤ L; rw [ha,hS₁]; exact inf_le_right
      exact Or.inl ⟨ha,(hk.odd_and_commutator_centralize K₀ P A₂ S hP
        (ctx.odd_card_of_le_hall_image _ hA₂B) (hA₂B.trans hBK₀)
        (hA₂L.trans ((le_centralizer_iff.mp hcomm).trans (centralizer_le hPL))) hSK₀).2⟩
    · have hPJ : P ≤ J := by change ⁅S,_⁆ ≤ J; rw [ha,hS₂]; exact inf_le_right
      exact Or.inr ⟨ha,(hk.odd_and_commutator_centralize K₀ P A₁ S hP
        (ctx.odd_card_of_le_hall_image _ hA₁B) (hA₁B.trans hBK₀)
        (hA₁L.trans (hcomm.trans (centralizer_le hPJ))) hSK₀).2⟩
  have hconj : P.map (MulAut.conj t).toMonoidHom ≤ centralizer (K₀ : Set G) := by
    rcases hresult with ⟨ha,hc⟩ | ⟨ha,hc⟩
    · change (⁅S,(B ⊓ K).map H.subtype⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom ≤ _
      rw [ha,hS₁,map_inf _ _ _ (MulAut.conj t).injective,hSm,←hS₂]
      exact le_sup_left.trans hc
    · change (⁅S,(B ⊓ K).map H.subtype⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom ≤ _
      rw [ha,hS₂,map_inf _ _ _ (MulAut.conj t).injective,hSm,hswap,←hS₁]
      exact le_sup_left.trans hc
  have hne := conjugate_ne_of_sylow_centralized K₀ P hk hzk hP t hconj
  have htH : t ∈ H := ctx.hstar.1.1.2 ht
  let u : H := ⟨t,htH⟩
  have hm : (K.map (MulAut.conj u).toMonoidHom).map H.subtype =
      K₀.map (MulAut.conj t).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have hneH : K ≠ K.map (MulAut.conj u).toMonoidHom := by
    intro he
    apply hne
    rw [←hm,←he]
  have hc := blocks_commute (RankOne.ChiProduct.blockCommutationHypothesis_of_fitting
    (source_hstar_fitting_eq_core D ctx.hstar)) hbK (hbK.map_equiv (MulAut.conj u)) hneH
  have hcm := congrArg (map H.subtype) hc
  rw [map_commutator,Subgroup.map_bot,hm] at hcm
  exact ⟨hresult,hne,commutator_eq_bot_iff_le_centralizer.mp hcm⟩

/-- The same selected component now carries the actual opposite-Borel geometry, with no new premise. -/
theorem Context.component_with_opposite_borel_geometry
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    let S := T.subtype ctx.hstar.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let B₀ := baumann (S : Subgroup H)
    ∃ (E : BinaryField) (K : Subgroup H),
      Nat.card E.Carrier = Nat.card F ∧ K.IsCComponent ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,E.Carrier)) ∧
      U ≤ normalizer (K : Set H) ∧ B₀ ≤ normalizer (K : Set H) ∧
      InLocalClass (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right)) ∧
      (localV (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right))).map (K ⊔ B₀).subtype =
        (⁅U,K⁆ : Subgroup H) ⊔ (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) ∧
      thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H) ≠ ⊥ ∧
      K ⊔ (S : Subgroup H) = ⊤ ∧
      (∃ t ∈ (S : Subgroup H), pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) ∧
      Nat.card (B ⊓ K : Subgroup H) = Nat.card F - 1 ∧ IsCyclic (B ⊓ K : Subgroup H) ∧
      B ≤ normalizer (K : Set H) ∧
      (∀ t : H, B ≤ normalizer (K.map (MulAut.conj t).toMonoidHom : Set H)) ∧
      ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∧
      ChapterC.IsL2EvenBlock L n ∧ pCore 2 L = ChapterC.blockU L ∧ center L = ⊥ ∧
      (∀ A : Subgroup G, A ≤ L → A ≤ B.map H.subtype → A ≠ ⊥ →
        ⁅baumann (T : Subgroup G),A⁆ = baumann (T : Subgroup G) ⊓ L ∧
        Chapter1.IsSylowIn 2 ⁅baumann (T : Subgroup G),A⁆ L ∧
        A ⊓ centralizer ((⁅baumann (T : Subgroup G),A⁆ : Subgroup G) : Set G) = ⊥ ∧
        IsSQTK KnownSimple.IsKnownSimple
          (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G))) ∧
      ChapterC.IsBlock K ∧ ChapterC.IsL2EvenBlock K n ∧
      pCore 2 K = ChapterC.blockU K ∧ center K = ⊥ ∧
      Chapter1.IsSylowIn 2 (B₀ ⊓ K) K ∧
      ⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆ =
        baumann (T : Subgroup G) ⊓ K.map H.subtype ∧
      Chapter1.IsSylowIn 2 ⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆
        (K.map H.subtype) ∧
    ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
      ∃ a : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)),
        (∀ l : L, a (QuotientGroup.mk' _ ⟨l,le_componentOrbit L T l.property⟩) =
          (e (QuotientGroup.mk' _ l),1)) ∧
        (∀ l : L, a (QuotientGroup.mk' _ (originalConjugateOrbitInclusion ht l)) =
          (1,e (QuotientGroup.mk' _ l))) ∧
    let C := B.map H.subtype
    let hCR : C ≤ localOrbit T L := hBB.trans ((map_subtype_le _).trans inf_le_left)
    let f := (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))).comp (inclusion hCR)
    let A₁ := ((MonoidHom.snd _ _).comp f).ker.map C.subtype
    let A₂ := ((MonoidHom.fst _ _).comp f).ker.map C.subtype
    ((B ⊓ K).map H.subtype = A₁ ∨ (B ⊓ K).map H.subtype = A₂) ∧
      A₁ ≤ L ∧ A₂ ≤ L.map (MulAut.conj t).toMonoidHom ∧
      Nat.card A₁ = Nat.card F - 1 ∧ Nat.card A₂ = Nat.card F - 1 ∧
      Disjoint A₁ A₂ ∧ A₁ ⊔ A₂ = C ∧ IsCyclic A₁ ∧ IsCyclic A₂ ∧
      (⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆ ≤ K.map H.subtype ⊓ L ∨
        ⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆ ≤
          K.map H.subtype ⊓ L.map (MulAut.conj t).toMonoidHom) ∧
      (((B ⊓ K).map H.subtype = A₁ ∧
        (⁅baumann (T : Subgroup G),A₂⁆ ⊔ A₂ : Subgroup G) ≤ centralizer (K.map H.subtype : Set G)) ∨
       ((B ⊓ K).map H.subtype = A₂ ∧
        (⁅baumann (T : Subgroup G),A₁⁆ ⊔ A₁ : Subgroup G) ≤ centralizer (K.map H.subtype : Set G))) ∧
      (K.map H.subtype).map (MulAut.conj t).toMonoidHom ≠ K.map H.subtype ∧
      K.map H.subtype ≤ centralizer ((K.map H.subtype).map (MulAut.conj t).toMonoidHom : Set G) ∧
      ¬ K.map H.subtype ≤ D.maximalLocal := by
  obtain ⟨E,K,hE,hK,heq,hUK,hBK,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,hbL,hnatL,hcoreL,hzL,hborelL,hbK,hnatK,hcoreK,hzK,hSK,haxis,haxisS,
    t,ht,htn,a,hfirst,hsecond,hor,hA₁L,hA₂L,hcard₁,hcard₂,hdis,hjoin,hcy₁,hcy₂,hcommon⟩ :=
    ctx.component_with_both_block_geometry D n hn hF e mark hBB
  let C := B.map H.subtype
  have hCR : C ≤ localOrbit T L := hBB.trans ((map_subtype_le _).trans inf_le_left)
  let f := (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))).comp (inclusion hCR)
  let A₁ := ((MonoidHom.snd _ _).comp f).ker.map C.subtype
  let A₂ := ((MonoidHom.fst _ _).comp f).ker.map C.subtype
  have hne₁ : A₁ ≠ ⊥ := by
    intro he
    change Nat.card A₁ = Nat.card F - 1 at hcard₁
    rw [he,card_bot,hF] at hcard₁
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hp
    omega
  have hne₂ : A₂ ≠ ⊥ := by
    intro he
    change Nat.card A₂ = Nat.card F - 1 at hcard₂
    rw [he,card_bot,hF] at hcard₂
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hp
    omega
  obtain ⟨hop,hne,hcomm⟩ := ctx.aligned_opposite_borel_centralizes D n hn hF e mark hBB
    hbL K hbK hzK hBK hBN haxisS ht htn A₁ A₂ hA₁L hA₂L
    (map_subtype_le _) (map_subtype_le _) hne₁ hne₂ hor
  have hout : ¬ K.map H.subtype ≤ D.maximalLocal := by
    intro hKM
    apply ctx.hstar.1.2
    have hjoinM : (K ⊔ (T.subtype ctx.hstar.1.1.2 : Subgroup H)).map H.subtype ≤ D.maximalLocal := by
      have hTm : (T.subtype ctx.hstar.1.1.2 : Subgroup H).map H.subtype = (T : Subgroup G) :=
        map_subgroupOf_eq_of_le ctx.hstar.1.1.2
      rw [Subgroup.map_sup,hTm]
      exact sup_le hKM (le_normalizer_componentOrbit L T)
    simpa only [hgen,←MonoidHom.range_eq_map,range_subtype] using hjoinM
  exact ⟨E,K,hE,hK,heq,hUK,hBK,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,hbL,hnatL,hcoreL,hzL,hborelL,hbK,hnatK,hcoreK,hzK,hSK,haxis,haxisS,
    t,ht,htn,a,hfirst,hsecond,hor,hA₁L,hA₂L,hcard₁,hcard₂,hdis,hjoin,hcy₁,hcy₂,hcommon,
    hop,hne,hcomm,hout⟩

end CFSG.Quasithin.Chapter10.MovingHall
