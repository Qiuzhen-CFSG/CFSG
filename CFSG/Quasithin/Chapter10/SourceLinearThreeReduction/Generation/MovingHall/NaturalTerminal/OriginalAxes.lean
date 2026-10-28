module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.MarkedAxis
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.HallTorus
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.ComponentHall
public import Theory.GroupTheory.PResidual.OddSubgroupLift
/-!
# The selected component's Hall intersection is an original full Cartan axis

The nonzero alpha fixed subgroup selects a coordinate kernel in the original
marked orbit quotient. Its known order equals the full kernel order, so
containment is equality. Odd containment through the two-core then lifts both
axes into L and its prescribed Sylow conjugate, without a block hypothesis.

The actual application keeps the same H-star component, its field order,
local-class data, residual cover, Hall normalization and block alternative.
Baum(T) normalizes both original factors and that component; consequently
its literal commutator with the selected axis lies in their intersection.
Natural marking and original Borel placement remain inputs owned by the
moving-Hall assembly, as do the subsequent block and terminal geometry.
Source: Aschbacher–Smith 10.2.3(4), printed pp.746–747.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]
local instance originalAxesFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
local instance originalAxesMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
set_option backward.isDefEq.respectTransparency false
/-- Full order upgrades marked-axis containment to equality in the original Hall. -/
theorem Context.original_full_axis_of_alpha_fixed
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (P : Subgroup G) (hPB : P ≤ B.map H.subtype)
    (hfixed : thompsonAlpha (T : Subgroup G) ⊓ centralizer (P : Set G) ≠ ⊥)
    (hcard : Nat.card P = Nat.card F - 1) :
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
    (P = A₁ ∨ P = A₂) ∧ Nat.card A₁ = Nat.card F - 1 ∧
      Nat.card A₂ = Nat.card F - 1 ∧ Disjoint A₁ A₂ ∧ A₁ ⊔ A₂ = C ∧
      IsCyclic A₁ ∧ IsCyclic A₂ := by
  obtain ⟨⟨c⟩,t,ht,htn,hcross⟩ := mark
  have mark : NaturalMarking D e := ⟨⟨c⟩,t,ht,htn,hcross⟩
  obtain ⟨a,hfirst,hsecond⟩ := source_original_natural_pair_quotient D n hn hF e ctx.nonnormal ht htn
  let C := B.map H.subtype
  have hCR : C ≤ localOrbit T L := hBB.trans ((map_subtype_le _).trans inf_le_left)
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))
  let f := q.comp (inclusion hCR)
  let A₁ := ((MonoidHom.snd _ _).comp f).ker.map C.subtype
  let A₂ := ((MonoidHom.fst _ _).comp f).ker.map C.subtype
  obtain ⟨_,h₂,h₁,hd,hgen,hcy₂,hcy₁⟩ := ctx.hall_torus_of_quotient D n hn hF e mark hBB a
  have haxis := ctx.original_marked_axis_of_alpha_fixed D n hn hF e c ht htn hcross hCR q
    hfirst hsecond P hPB hfixed
  have hP : P = A₁ ∨ P = A₂ := by
    rcases haxis with hh | hh
    · right
      apply eq_of_le_of_card_ge
      · intro p hp
        obtain ⟨r,hr,he⟩ := hh hp
        have her : r = (⟨p,hCR (hPB hp)⟩ : localOrbit T L) := Subtype.ext he
        subst r
        exact mem_map.mpr ⟨⟨p,hPB hp⟩,hr,rfl⟩
      · rw [h₂,hcard]
    · left
      apply eq_of_le_of_card_ge
      · intro p hp
        obtain ⟨r,hr,he⟩ := hh hp
        have her : r = (⟨p,hCR (hPB hp)⟩ : localOrbit T L) := Subtype.ext he
        subst r
        exact mem_map.mpr ⟨⟨p,hPB hp⟩,hr,rfl⟩
      · rw [h₁,hcard]
  exact ⟨t,ht,htn,a,hfirst,hsecond,hP,h₁,h₂,hd.symm,(sup_comm _ _).trans hgen,hcy₁,hcy₂⟩


include D in
omit [Finite F] [CharP F 2] in
/-- Both odd axes of any original marked pair quotient lie in the actual components. -/
theorem source_natural_odd_axes_le_factors
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {t : G} (ht : t ∈ (T : Subgroup G))
    (q : localOrbit T L →* (SL(2,F) × SL(2,F)))
    (hk : q.ker = pCore 2 (localOrbit T L))
    (hfirst : ∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1))
    (hsecond : ∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l)))
    (C : Subgroup G) (hCR : C ≤ localOrbit T L) (ho : Odd (Nat.card C)) :
    let f := q.comp (inclusion hCR)
    ((MonoidHom.snd _ _).comp f).ker.map C.subtype ≤ L ∧
      ((MonoidHom.fst _ _).comp f).ker.map C.subtype ≤ L.map (MulAut.conj t).toMonoidHom := by
  let R := localOrbit T L
  let A := L.subgroupOf R
  let J := L.map (MulAut.conj t).toMonoidHom
  have hLR : L ≤ R := le_componentOrbit L T
  have hJR : J ≤ R := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hLR
    have hRm : R.map (MulAut.conj t).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
    rwa [hRm] at hh
  have hA : A.IsCComponent := D.maximal.1.1.subgroupOf_of_le hLR (componentOrbit_le_sup L T)
  have hpA : IsPPerfect 2 A := D.faithful.1.2.1.of_surjective
    (subgroupOfEquivOfLe hLR).symm.toMonoidHom (subgroupOfEquivOfLe hLR).symm.surjective
  let τ := originalOrbitConjugation (L := L) ht
  have hJmap : A.map τ.toMonoidHom = J.subgroupOf R := by
    apply map_injective R.subtype_injective
    rw [map_map,show R.subtype.comp τ.toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp R.subtype from rfl,←map_map,
      map_subgroupOf_eq_of_le hLR,map_subgroupOf_eq_of_le hJR]
  let aJ : A ≃* J.subgroupOf R := (τ.subgroupMap A).trans (MulEquiv.subgroupCongr hJmap)
  have hJ : (J.subgroupOf R).IsSubnormal := hJmap ▸ (hA.map_equiv τ).subnormal
  have hpJ : IsPPerfect 2 (J.subgroupOf R) := hpA.of_surjective aJ.toMonoidHom aJ.surjective
  let P := ((MonoidHom.snd _ _).comp (q.comp (inclusion hCR))).ker.map C.subtype
  let Q := ((MonoidHom.fst _ _).comp (q.comp (inclusion hCR))).ker.map C.subtype
  have hPC : P ≤ C := map_subtype_le _
  have hQC : Q ≤ C := map_subtype_le _
  have hPR := hPC.trans hCR
  have hQR := hQC.trans hCR
  have hP : P.subgroupOf R ≤ A := by
    apply odd_le_of_map_le_of_ker_eq_twoCore (P.subgroupOf R) A
      (by rw [Nat.card_congr (subgroupOfEquivOfLe hPR).toEquiv]
          exact ho.of_dvd_nat (card_dvd_of_le hPC)) hA.subnormal hpA q hk
    rintro _ ⟨p,hp,rfl⟩
    obtain ⟨c,hc,he⟩ := hp
    have hc' : (q (inclusion hCR c)).2 = 1 := hc
    have he' : inclusion hCR c = p := Subtype.ext he
    rw [he'] at hc'
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) (q p).1
    refine mem_map.mpr ⟨⟨l,hLR l.property⟩,l.property,?_⟩
    rw [hfirst]
    exact Prod.ext hl hc'.symm
  have hQ : Q.subgroupOf R ≤ J.subgroupOf R := by
    apply odd_le_of_map_le_of_ker_eq_twoCore (Q.subgroupOf R) (J.subgroupOf R)
      (by rw [Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv]
          exact ho.of_dvd_nat (card_dvd_of_le hQC)) hJ hpJ q hk
    rintro _ ⟨p,hp,rfl⟩
    obtain ⟨c,hc,he⟩ := hp
    have hc' : (q (inclusion hCR c)).1 = 1 := hc
    have he' : inclusion hCR c = p := Subtype.ext he
    rw [he'] at hc'
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) (q p).2
    refine mem_map.mpr ⟨originalConjugateOrbitInclusion ht l,?_,?_⟩
    · exact mem_map.mpr ⟨l,l.property,rfl⟩
    · rw [hsecond]
      exact Prod.ext hc'.symm hl
  exact ⟨fun p hp => hP (show (⟨p,hPR hp⟩ : R) ∈ P.subgroupOf R from hp),
    fun p hp => hQ (show (⟨p,hQR hp⟩ : R) ∈ Q.subgroupOf R from hp)⟩

open ChapterB.SourceInduction ChapterB.QuasisimpleSource ChapterC.GlaubermanNiles
/-- The original paired source makes Baum(T) normalize the actual component. -/
theorem Context.baumann_normalizes_original
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    baumann (T : Subgroup G) ≤ normalizer (L : Set G) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let A := L.subgroupOf X
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  have hB := (ctx.original_common_baumann_embedding D n hn hF e).2.1
  have hmap : (baumann (S : Subgroup X)).map X.subtype = baumann (T : Subgroup G) := by
    have hh := baumann_map_injective X.subtype X.subtype_injective (S : Subgroup X)
    change (baumann (S : Subgroup X)).map X.subtype =
      baumann ((S : Subgroup X).map X.subtype) at hh
    rw [show (S : Subgroup X).map X.subtype = (T : Subgroup G) from
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)] at hh
    exact hh
  have hh := (map_mono (f := X.subtype) hB).trans (A.le_normalizer_map X.subtype)
  rwa [hmap,map_subgroupOf_eq_of_le hLX] at hh

/-- The same selected comparison component meets the original Hall in a full
original axis, retaining its block alternative and Baumann local structure. -/
theorem Context.component_with_original_axis
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
      (ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∨
        (ChapterC.IsBlock K ∧ ∃ m, ChapterC.IsL2EvenBlock K m)) ∧
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
          K.map H.subtype ⊓ L.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨d,E,hE,hmarked,K,hK,hi,hcan,hUK,hBK,hlocal,hv,hfixed,heq,hgen,hcover,
    hdiv,hcard,hcyclic,hBN,hBNt,hblock,_⟩ := ctx.paired_component_with_full_hall D n hn hF e mark hBB
  have hfixedG := alpha_fixed_subtype_nontrivial T H ctx.hstar.1.1.2 K hfixed
  have hfixedP : thompsonAlpha (T : Subgroup G) ⊓
      centralizer ((B ⊓ K).map H.subtype : Set G) ≠ ⊥ := by
    intro he
    exact hfixedG (bot_unique ((inf_le_inf_left _ (centralizer_le (map_mono inf_le_right))).trans he.le))
  have hcardP : Nat.card ((B ⊓ K).map H.subtype) = Nat.card F - 1 := by
    rw [card_map_of_injective H.subtype_injective,hcard]
  obtain ⟨t,ht,htn,a,hfirst,hsecond,haxis,h₁,h₂,hd,hjoin,hcy₁,hcy₂⟩ :=
    ctx.original_full_axis_of_alpha_fixed D n hn hF e mark hBB
      ((B ⊓ K).map H.subtype) (map_mono inf_le_left) hfixedP hcardP
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))
  have hk : q.ker = pCore 2 (localOrbit T L) := by
    ext r
    change a (QuotientGroup.mk' _ r) = 1 ↔ _
    rw [a.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff r
  obtain ⟨hL,hLt⟩ := source_natural_odd_axes_le_factors D e ht q hk hfirst hsecond
    (B.map H.subtype) (hBB.trans ((map_subtype_le _).trans inf_le_left))
    (ctx.odd_card_of_le_hall_image _ le_rfl)
  have hBL := ctx.baumann_normalizes_original D n hn hF e
  have hBLt : baumann (T : Subgroup G) ≤
      normalizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hBL
    have hSm : (baumann (T : Subgroup G)).map (MulAut.conj t).toMonoidHom =
        baumann (T : Subgroup G) := mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_baumann _ ((T : Subgroup G).le_normalizer ht))
    rwa [hSm,map_normalizer_eq_of_bijective L (MulAut.conj t).bijective] at hh
  have hBK' : baumann (T : Subgroup G) ≤ normalizer (K.map H.subtype : Set G) := by
    have hm : (baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H)).map H.subtype =
        baumann (T : Subgroup G) := by
      have hh := baumann_map_injective H.subtype H.subtype_injective
        (T.subtype ctx.hstar.1.1.2 : Subgroup H)
      change (baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H)).map H.subtype =
        baumann ((T.subtype ctx.hstar.1.1.2 : Subgroup H).map H.subtype) at hh
      rw [show (T.subtype ctx.hstar.1.1.2 : Subgroup H).map H.subtype = (T : Subgroup G) from
        map_subgroupOf_eq_of_le ctx.hstar.1.1.2] at hh
      exact hh
    have hh := (map_mono (f := H.subtype) hBK).trans (K.le_normalizer_map H.subtype)
    rwa [hm] at hh
  have hcommonK : ⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆ ≤ K.map H.subtype :=
    (commutator_mono le_rfl (map_mono inf_le_right)).trans
      (le_normalizer_iff_commutator_le_right.mp hBK')
  refine ⟨E,K,hE,hK,heq,hUK,hBK,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,hblock,t,ht,htn,a,hfirst,hsecond,haxis,hL,hLt,h₁,h₂,hd,hjoin,hcy₁,hcy₂,?_⟩
  rcases haxis with ha | ha
  · left
    exact le_inf hcommonK ((commutator_mono le_rfl (ha.le.trans hL)).trans
      (le_normalizer_iff_commutator_le_right.mp hBL))
  · right
    exact le_inf hcommonK ((commutator_mono le_rfl (ha.le.trans hLt)).trans
      (le_normalizer_iff_commutator_le_right.mp hBLt))

end CFSG.Quasithin.Chapter10.MovingHall
