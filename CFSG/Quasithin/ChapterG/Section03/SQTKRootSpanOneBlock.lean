module

public import CFSG.Quasithin.ChapterG.Section03.SQTKCoreFreeBlocks
public import CFSG.Quasithin.ChapterG.Section03.RootSpanTwoBlockWreath
public import CFSG.Quasithin.ChapterG.Section03.RootSpanOneBlockActor
import Theory.SpecificGroups.PSL3Two.WreathCubicSylowObstruction
import Theory.GroupTheory.PPerfectCubicImage

/-!
# The single full actor on the actual total root span

The root seed remains faithful on the total span. Its commutator generation
therefore keeps the actual cubic residual nontrivial after restriction.
The marked two-block wreath obstruction, with the image of the supplied
Sylow subgroup, excludes two blocks. The remaining block fills the exact
restriction image. The whole original actor's pointwise kernel is retained.

Source: Aschbacher--Smith12.7.18, printed p.845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03
universe u
variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {X : Type u} [Group X] [Finite X]

private theorem image_nontrivial {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (f : G →* H) (hne : A≠⊥)
    (hi : Function.Injective (f.comp A.subtype)) : A.map f≠⊥ := by
  intro hb
  apply hne
  apply _root_.eq_bot_iff.mpr
  intro a ha
  have hm : f a=1 := mem_bot.mp (hb ▸ mem_map_of_mem f ha)
  have he : (⟨a,ha⟩ : A)=1 := hi (by simpa using hm)
  exact congrArg Subtype.val he

private theorem cubic_image {G H : Type*} [Group G] [Group H]
    (J : Subgroup G) (hJ : IsPPerfect 2 J) (hc : Nat.card (J ⧸ pCore 2 J)=3)
    (f : G →* H) (hne : J.map f≠⊥) :
    IsPPerfect 2 (J.map f) ∧ Nat.card ((J.map f) ⧸ pCore 2 (J.map f))=3 := by
  have hn : f.subgroupMap J≠1 := by
    intro he
    apply hne
    apply _root_.eq_bot_iff.mpr
    rintro y ⟨j,hj,rfl⟩
    exact congrArg Subtype.val (congrArg (fun q : J →* J.map f => q ⟨j,hj⟩) he)
  exact ⟨hJ.of_surjective _ (f.subgroupMap_surjective J),
    cubic_core_quotient_of_twoPerfect_image hJ hc _ (f.subgroupMap_surjective J) hn⟩

/-- Actual root and cubic seeds force one full block in the literal total span.
Only the root-generated group, and hence the supplied root seed, is asserted
faithful under restriction. -/
theorem sqtk_root_span_one_block
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (Q : Subgroup (BinaryLinear.GL V)) (q : X →* Q) (hq : Function.Surjective q)
    (x : V) (hsource : Hypotheses Q (MulAction.orbit Q x)) (hcore : pCore 2 Q=⊥)
    (hf : FullAction Q (MulAction.orbit Q x))
    (hd : Decomposition Q (MulAction.orbit Q x))
    (hl : LocalStructure Q (MulAction.orbit Q x))
    (A J : Subgroup Q) (hA : A.map Q.subtype≤rootGroup Q x) (hne : A≠⊥)
    (hmove : A=⁅A,J⁆) (hJ : IsPPerfect 2 J) (hc : Nat.card (J ⧸ pCore 2 J)=3)
    (T : Sylow 2 Q) (hTJ : (T : Subgroup Q)≤normalizer (J : Set Q)) :
    let S := Submodule.span (ZMod 2) (MulAction.orbit Q x)
    ∃hpar : Q≤parabolic S,
      let ρ := action Q S hpar
      ρ.ker=fixingKernel Q S ∧
      Function.Injective (ρ.comp (Subgroup.inclusion (generated_le Q (MulAction.orbit Q x)))) ∧
      Function.Injective (ρ.comp A.subtype) ∧
      Nat.card (OrbitBlock Q (MulAction.orbit Q x))=1 ∧
      ρ.range=⊤ ∧ Nat.card (A.map ρ)=Nat.card A ∧
      (Module.finrank (ZMod 2) S=3 ∨ Module.finrank (ZMod 2) S=4 ∨ Module.finrank (ZMod 2) S=5) ∧
      A.map ρ≤radical (centerLine (⟨x,Submodule.subset_span (MulAction.mem_orbit_self x)⟩ : S)) ∧
      A.map ρ=⁅A.map ρ,J.map ρ⁆ ∧
      IsPPerfect 2 (J.map ρ) ∧ Nat.card ((J.map ρ) ⧸ pCore 2 (J.map ρ))=3 := by
  classical
  let Δ := MulAction.orbit Q x
  let S := Submodule.span (ZMod 2) Δ
  obtain ⟨hp,hformula,hker,hgeninj⟩ := root_span_action hsource hcore
  let ρ := action Q S hp
  have hAgen (a : A) : (a.val:BinaryLinear.GL V)∈generated Q Δ :=
    rootGroup_le_generated Q (MulAction.mem_orbit_self x)
      (hA (mem_map_of_mem Q.subtype a.property))
  have hAinj : Function.Injective (ρ.comp A.subtype) := by
    intro a b hab
    have hh : (⟨a.val.val,hAgen a⟩ : generated Q Δ)=⟨b.val.val,hAgen b⟩ := hgeninj hab
    exact Subtype.ext (Subtype.ext (congrArg (fun g : generated Q Δ => g.val) hh))
  have hAimage : A.map ρ≠⊥ := image_nontrivial A ρ hne hAinj
  have hcomm : A.map ρ=⁅A.map ρ,J.map ρ⁆ := by rw [←map_commutator,←hmove]
  have hJimage : J.map ρ≠⊥ := by
    intro he
    exact hAimage (by simpa only [he,commutator_bot_right] using hcomm)
  have hone : Nat.card (OrbitBlock Q Δ)=1 := by
    have hcount := sqtk_core_free_block_count hX Q q hq x hsource hcore hf hd hl
    let i : OrbitBlock Q Δ := ⟨MulAction.orbit (generated Q Δ) x,x,MulAction.mem_orbit_self x,rfl⟩
    let : Nonempty (OrbitBlock Q Δ) := ⟨i⟩
    let : Finite (OrbitBlock Q Δ) := Finite.of_injective
      (fun k : OrbitBlock Q Δ => k.val) Subtype.val_injective
    have hpos : 0<Nat.card (OrbitBlock Q Δ) := Nat.card_pos
    by_contra hnot
    have htwo : Nat.card (OrbitBlock Q Δ)=2 := by
      change Nat.card (OrbitBlock Q Δ)≤2 at hcount
      omega
    have hthree (i : OrbitBlock Q Δ) : Module.finrank (ZMod 2) (blockSpace Q Δ i)=3 := by
      obtain ⟨j,hji,_⟩ := (Nat.card_eq_two_iff' i).mp htwo
      exact sqtk_core_free_block_dimension_three hX Q q hq x hsource hcore hf hd hl i j hji.symm
    obtain ⟨hp',_,_,_,_,_,_,e,_⟩ := root_span_two_block_wreath Q x hsource hcore hf hd htwo hthree
    let r := e.toMonoidHom.comp ρ.rangeRestrict
    have hr : Function.Surjective r := e.surjective.comp ρ.rangeRestrict_surjective
    have hAr : A.map r≠⊥ := image_nontrivial A r hne (by
      intro a b he
      apply hAinj
      exact congrArg Subtype.val (e.injective he))
    have hJr : J.map r≠⊥ := by
      intro he
      have hm : A.map r=⁅A.map r,J.map r⁆ := by rw [←map_commutator,←hmove]
      exact hAr (by simpa only [he,commutator_bot_right] using hm)
    obtain ⟨hpJ,hcJ⟩ := cubic_image J hJ hc r hJr
    let T' := T.mapSurjective hr
    have hn : (T' : Subgroup Matrix.PSL3Two.WreathPair.Actor)≤normalizer (J.map r : Set _) :=
      (map_mono hTJ).trans (le_normalizer_map r)
    exact Matrix.PSL3Two.WreathPair.not_sylow_normalized_cubic_residual (J.map r) T' hpJ hcJ hn
  obtain ⟨hp',hfull,hspaces⟩ := root_span_one_block_actor hsource hcore hf hd hone
  have hcard : Nat.card (A.map ρ)=Nat.card A := by
    let eA := MulEquiv.ofBijective (ρ.subgroupMap A)
      ⟨fun a b he => hAinj (congrArg Subtype.val he),ρ.subgroupMap_surjective A⟩
    exact Nat.card_congr eA.toEquiv.symm
  have hdim : Module.finrank (ZMod 2) S=3 ∨ Module.finrank (ZMod 2) S=4 ∨ Module.finrank (ZMod 2) S=5 := by
    obtain ⟨i,_⟩ := Nat.card_eq_one_iff_exists.mp hone
    have hh := (sqtk_core_free_block_lifts hX Q q hq x hsource hcore hf hd hl i).1
    rw [hspaces i] at hh
    change 3≤Module.finrank (ZMod 2) S ∧ Module.finrank (ZMod 2) S≤5 at hh
    omega
  have hroot : A.map ρ≤radical (centerLine (⟨x,Submodule.subset_span (MulAction.mem_orbit_self x)⟩ : S)) := by
    rintro _ ⟨g,hg,rfl⟩
    have hgroot := hA (mem_map_of_mem Q.subtype hg)
    refine ⟨?_,?_⟩
    · intro w hw
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
      apply Subtype.ext
      exact hgroot.2.1 _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
    · intro w
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hgroot.2.2 (w:V))
      exact Submodule.mem_span_singleton.mpr ⟨c,Subtype.ext hc⟩
  obtain ⟨hJp,hJc⟩ := cubic_image J hJ hc ρ hJimage
  exact ⟨hp,hker,hgeninj,hAinj,hone,hfull,hcard,hdim,hroot,hcomm,hJp,hJc⟩

end CFSG.Quasithin.ChapterG.Section03
