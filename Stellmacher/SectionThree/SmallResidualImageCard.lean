module
public import Stellmacher.SectionThree.ResidualImageIrreducible
public import Stellmacher.TwoResidualIdentification

/-!
# Small residual images survive a noncentral quotient action

For a solvable Section Three local group, let f be surjective and suppose
g factors through f without killing the two-residual. If the residual image
under f has order five or is elementary abelian of exponent three, then g
preserves that image's cardinality. Neither representation is assumed faithful.

Factor g through f and intersect the induced kernel with the original
residual image. The intersection is proper because g is nontrivial on the
residual. In order five, Lagrange's theorem makes it trivial. In the
three-elementary case, (3.3)'s residual-image irreducibility makes the
invariant intersection trivial. Thus the induced map is injective on the
residual, and its actual image has unchanged cardinality.

This consequence of (3.3) supplies the odd-image comparison in Stellmacher
(10.1)(15), printed p.63, when the terminal quotient acts on a noncentral
chief section. The source14 models have orders five and nine; the latter
is elementary abelian of exponent three.
-/

namespace Stellmacher.SectionThree
universe u v w

public theorem pSet_small_residual_image_card_eq
    {G : Type u} {X : Type v} {Y : Type w}
    [Group G] [Finite G] [Group X] [Finite X] [Group Y] [Finite Y]
    (S : Subgroup G) (hyp : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (f : P →* X) (hsurj : Function.Surjective f) (g : P →* Y)
    (hker : f.ker ≤ g.ker) (hres : ¬ twoResidualSubgroup P ≤ g.ker)
    (hsmall : Nat.card ((twoResidualSubgroup P).map f)=5 ∨
      IsElementaryAbelian 3 ((twoResidualSubgroup P).map f)) :
    Nat.card ((twoResidualSubgroup P).map g)=Nat.card ((twoResidualSubgroup P).map f) := by
  let R := (twoResidualSubgroup P).map f
  let beta : X →* Y := f.liftOfSurjective hsurj ⟨g,hker⟩
  have hcomp (a:P) : beta (f a)=g a :=
    f.liftOfRightInverse_comp_apply (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨g,hker⟩ a
  have hcompHom : beta.comp f=g := MonoidHom.ext hcomp
  have hRnot : ¬ R ≤ beta.ker := by
    intro hR
    apply hres
    intro a ha
    apply MonoidHom.mem_ker.mpr
    rw [←hcomp]
    exact MonoidHom.mem_ker.mp (hR (Subgroup.mem_map_of_mem f ha))
  have hRne : R≠⊥ := fun hh => hRnot (hh ▸ bot_le)
  let K := beta.ker ⊓ R
  have hKR : K ≤ R := inf_le_right
  have hKnot : K≠R := fun heq => hRnot (heq ▸ (show K≤beta.ker from inf_le_left))
  have hKbot : K=⊥ := by
    rcases hsmall with hcard | helem
    · have hdiv : Nat.card K ∣ 5 := by
        have hh := Subgroup.card_dvd_of_le hKR
        rwa [hcard] at hh
      rcases (show Nat.Prime 5 by decide).eq_one_or_self_of_dvd _ hdiv with hone | hfive
      · exact Subgroup.card_eq_one.mp hone
      · exact (hKnot (Subgroup.eq_of_le_of_card_ge hKR (by rw [hcard,hfive]))).elim
    · have hnormal : (twoResidualSubgroup P).Normal := by
        rw [twoResidualSubgroup_eq_hktPResidual' P]
        exact BenderSuzuki.External.hktPResidual_normal
      let _ : R.Normal := hnormal.map f hsurj
      have hirr := pSet_residual_image_irreducible S hyp P hP hsolv f R rfl hRne helem
      have hstable : IsConjugateInvariantBy K ((S.subgroupOf P).map f) := by
        intro s a ha
        exact ⟨(inferInstance : beta.ker.Normal).conj_mem a ha.1 s,
          (inferInstance : R.Normal).conj_mem a ha.2 s⟩
      exact (hirr.2.2 K bot_le hKR hstable).resolve_right hKnot
  let r : R →* Y := beta.comp R.subtype
  have hrinj : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    apply Subtype.ext
    have hmem : (a:X)∈K := ⟨ha,a.property⟩
    rw [hKbot,Subgroup.mem_bot] at hmem
    exact hmem
  have hrange : r.range=R.map beta := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  have himage : R.map beta=(twoResidualSubgroup P).map g := by
    rw [Subgroup.map_map,hcompHom]
  rw [←himage,←hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hrinj).toEquiv).symm

end Stellmacher.SectionThree
