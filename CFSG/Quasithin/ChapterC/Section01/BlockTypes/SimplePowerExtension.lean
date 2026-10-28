module

public import CFSG.Quasithin.ChapterC.Section01.BlockDefs
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.IsSubnormal

/-!
# Short subgroups of two-group extensions of simple powers

A short subnormal subgroup in a two-group extension of a direct power of
one centerless simple group has that simple group as its quotient by O₂.
Two-perfection forces the subgroup into the normal layer. Subnormality
makes each coordinate image trivial or surjective, so the kernel is O₂.
The resulting faithful quotient has trivial center, and the short-group
quotient alternatives make a nonzero coordinate an isomorphism.

The argument adapts the checked A7 proof in
`ComponentRefinement/SurvivingIntersections/MathieuTwentyThree/BlockExclusion.lean`.
Source: Aschbacher–Smith C.1.7 and C.1.12, printed pp.123–124, applied in
2.3.9(7)(f), printed pp.525–526 (combined manuscript of 1 March 2004).
-/

public section
namespace CFSG.Quasithin.ChapterC
open Subgroup Theory.GroupTheory

/-- The coordinate dichotomy identifies the quotient of a short group with the simple factor.
The two-group kernel and the trivial center of the factor are both essential. -/
theorem IsShort.quotient_equiv_of_simple_coordinates {B T : Type*} [Group B]
    [Group T] [IsSimpleGroup T] (hB : IsShort B)
    (hTcenter : center T = ⊥) (hTtwo : ¬ IsPGroup 2 T) {n : ℕ} (g : B →* (Fin n → T))
    (hker : IsPGroup 2 g.ker)
    (hcoord : ∀ i, (Pi.evalMonoidHom _ i).comp g = 1 ∨
      Function.Surjective ((Pi.evalMonoidHom _ i).comp g)) :
    Nonempty ((B ⧸ pCore 2 B) ≃* T) := by
  let : Finite B := hB.finite
  -- A normal two-subgroup has trivial image in every nontrivial coordinate.
  have hcore : pCore 2 B = g.ker := by
    apply le_antisymm
    · intro b hb
      apply MonoidHom.mem_ker.mpr
      funext i
      rcases hcoord i with hi | hi
      · exact DFunLike.congr_fun hi b
      · let c := (Pi.evalMonoidHom _ i).comp g
        have : ((pCore 2 B).map c).Normal := Normal.map inferInstance c hi
        rcases (inferInstance : ((pCore 2 B).map c).Normal).eq_bot_or_eq_top with hh | hh
        · exact mem_bot.mp (hh ▸ mem_map_of_mem c hb)
        · have hp : IsPGroup 2 ((pCore 2 B).map c) := pCore_isPGroup.map c
          rw [hh] at hp
          exact (hTtwo (hp.of_equiv topEquiv)).elim
    · exact le_sSup ⟨inferInstance, hker⟩
  let qg := QuotientGroup.lift (pCore 2 B) g hcore.le
  have hqg : Function.Injective qg :=
    (QuotientGroup.injective_lift_iff _ _ _).mpr hcore
  -- Central elements vanish in every coordinate of the faithful quotient map.
  have hcenter : center (B ⧸ pCore 2 B) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    apply mem_bot.mpr
    apply hqg
    rw [map_one]
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
    change g b = 1
    funext i
    rcases hcoord i with hi | hi
    · exact DFunLike.congr_fun hi b
    · have hc : g b i ∈ center (T) := by
        rw [mem_center_iff]
        intro a
        obtain ⟨x, rfl⟩ := hi a
        have hh := congrArg (fun z => qg z i)
          (mem_center_iff.mp hz (QuotientGroup.mk' (pCore 2 B) x))
        simpa [qg] using hh
      simpa only [hTcenter,
        mem_bot, Pi.one_apply] using hc
  -- The genuine short-group alternatives are quasisimplicity or order three.
  have : IsSimpleGroup (B ⧸ pCore 2 B) := by
    rcases hB.quotient with hq | hq
    · let := hq
      let := IsQuasisimple.simple (G := B ⧸ pCore 2 B)
      exact ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
        (QuotientGroup.quotientBot)).symm.isSimpleGroup
    · exact isSimpleGroup_of_prime_card hq
  obtain ⟨z, hz⟩ := exists_ne (1 : B ⧸ pCore 2 B)
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
  have hgb : g b ≠ 1 := fun hh => hz (hqg (hh.trans (map_one qg).symm))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hgb
  have hsurj : Function.Surjective ((Pi.evalMonoidHom _ i).comp g) := by
    rcases hcoord i with ht | ht
    · exact (hi (DFunLike.congr_fun ht b)).elim
    · exact ht
  let c := (Pi.evalMonoidHom _ i).comp qg
  have hc : Function.Surjective c := by
    intro a
    obtain ⟨b, hb⟩ := hsurj a
    exact ⟨QuotientGroup.mk' (pCore 2 B) b, hb⟩
  have hci : Function.Injective c := by
    apply (MonoidHom.ker_eq_bot_iff c).mp
    rcases (inferInstance : c.ker.Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · have ht : c = 1 := MonoidHom.ker_eq_top_iff.mp hh
      obtain ⟨a, ha⟩ := exists_ne (1 : T)
      obtain ⟨z, rfl⟩ := hc a
      exact (ha (DFunLike.congr_fun ht z)).elim
  exact ⟨MulEquiv.ofBijective c ⟨hci, hc⟩⟩

/-- A short subgroup subnormal in a two-group extension of a simple power
has the specified simple quotient. All normality is relative to K. -/
theorem IsBlock.quotient_equiv_of_simple_power {K T : Type*} [Group K] [Group T]
    [IsSimpleGroup T] (hTcenter : center T = ⊥) (hTtwo : ¬ IsPGroup 2 T)
    {B : Subgroup K} (hB : IsBlock B) (N : Subgroup K) [N.Normal]
    (hquot : IsPGroup 2 (K ⧸ N)) {n : ℕ} (f : N →* (Fin n → T))
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    Nonempty ((B ⧸ pCore 2 B) ≃* T) := by
  have hBN : B ≤ N := by
    have hh := hB.short.twoPerfect.hom_eq_one_of_isPGroup hquot
      ((QuotientGroup.mk' N).comp B.subtype)
    intro b hb
    exact (QuotientGroup.eq_one_iff b).mp (DFunLike.congr_fun hh ⟨b, hb⟩)
  let g := f.comp (inclusion hBN)
  have hgker : IsPGroup 2 g.ker :=
    hker.comap_of_injective (inclusion hBN) (inclusion_injective hBN)
  have hcoord : ∀ i, (Pi.evalMonoidHom _ i).comp g = 1 ∨
      Function.Surjective ((Pi.evalMonoidHom _ i).comp g) := by
    intro i
    let c := (Pi.evalMonoidHom _ i).comp f
    have hc : Function.Surjective c := by
      intro a
      obtain ⟨x, hx⟩ := hf (fun _ => a)
      exact ⟨x, congrFun hx i⟩
    have hs : ((Pi.evalMonoidHom _ i).comp g).range.IsSubnormal := by
      have he : ((Pi.evalMonoidHom _ i).comp g).range = (B.subgroupOf N).map c := by
        rw [show (Pi.evalMonoidHom _ i).comp g = c.comp (inclusion hBN) from rfl,
          MonoidHom.range_comp, inclusion_range]
      rw [he]
      exact hB.subnormal.subgroupOf.map hc
    rcases hs.eq_bot_or_top_of_isSimpleGroup inferInstance with hh | hh
    · exact Or.inl (MonoidHom.range_eq_bot_iff.mp hh)
    · exact Or.inr (MonoidHom.range_eq_top.mp hh)
  exact hB.short.quotient_equiv_of_simple_coordinates hTcenter hTtwo g hgker hcoord

end CFSG.Quasithin.ChapterC
end
