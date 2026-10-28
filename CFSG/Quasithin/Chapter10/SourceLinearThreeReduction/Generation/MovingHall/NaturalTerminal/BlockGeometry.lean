module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.BlockCores

/-!
# Core and Sylow recovery on the same aligned source component

The original block alternative now retains its entire two-core and natural
module over the original field in either orientation. In the original-block
orientation the Hall axes supply the literal commutator Sylows, faithful
axis action and SQTK Borel normalizers. In the comparison orientation the
same selected K has its entire natural core and a full Baumann Sylow.
Both original quotient markings and the equality with the prescribed Hall
intersection are retained. The moving-Hall owner still owes simultaneous
blockhood and terminal overcomponent recognition, as well as the earlier
natural-row selection and original Borel placement.

Source: Aschbacher–Smith 10.2.3(4), printed p.747.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterB.QuasisimpleSource ChapterC.GlaubermanNiles
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]

/-- Discharge the core, natural-degree and Sylow premises for the actual
aligned block alternative; the terminal original-block clauses are proved
on the literal Hall subgroups and Baumann commutators. -/
theorem Context.component_with_block_core_geometry
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
      ((ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∧
        ChapterC.IsL2EvenBlock L n ∧ pCore 2 L = ChapterC.blockU L ∧ center L = ⊥ ∧
        ∀ A : Subgroup G, A ≤ L → A ≤ B.map H.subtype → A ≠ ⊥ →
          ⁅baumann (T : Subgroup G),A⁆ = baumann (T : Subgroup G) ⊓ L ∧
          Chapter1.IsSylowIn 2 ⁅baumann (T : Subgroup G),A⁆ L ∧
          A ⊓ centralizer ((⁅baumann (T : Subgroup G),A⁆ : Subgroup G) : Set G) = ⊥ ∧
          IsSQTK KnownSimple.IsKnownSimple
            (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G))) ∨
        (ChapterC.IsBlock K ∧ ChapterC.IsL2EvenBlock K n ∧
          pCore 2 K = ChapterC.blockU K ∧ center K = ⊥ ∧
          Chapter1.IsSylowIn 2 (B₀ ⊓ K) K)) ∧
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
  obtain ⟨E,K,hE,hK,heq,hUK,hBK,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,hblock,t,ht,htn,a,hfirst,hsecond,haxes⟩ :=
    ctx.component_with_original_axis D n hn hF e mark hBB
  have hBR := hBB.trans ((map_subtype_le _).trans inf_le_left)
  refine ⟨E,K,hE,hK,heq,hUK,hBK,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,?_,t,ht,htn,a,hfirst,hsecond,haxes⟩
  rcases hblock with hL | ⟨hb,hnat⟩
  · obtain ⟨hLn,hcore,hz⟩ := ctx.original_natural_block_core D n hn hF e mark hBR hL
    exact Or.inl ⟨hL,hLn,hcore,hz,
      fun A hAL hAB hne => ctx.original_block_axis_borel D n hn hF e mark hBB hL A hAL hAB hne⟩
  · have hR : pResidual 2 H = K ∨ ∃ t : H,
        pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom := by
      obtain ⟨t,_,he⟩ := hcover
      exact Or.inr ⟨t,he⟩
    exact Or.inr ⟨hb,ctx.comparison_natural_block_core D n hn hF e mark hBR
      K hb hnat hE heq.some hR⟩

end CFSG.Quasithin.Chapter10.MovingHall
