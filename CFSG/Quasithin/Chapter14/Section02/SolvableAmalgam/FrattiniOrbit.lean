module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NonabelianGeometry
public import Theory.Representation.ConjugateSpanOrbit
public import Theory.GroupTheory.PGroup.SmallFrattiniSingularIndex
public import Mathlib.Tactic

/-!
# The original binary Frattini orbit

For the selected nonabelian closure U=⟨V^H⟩, the point of order two is
exactly Φ(U). The plane has one nonzero image in U/Φ(U), fixed by its
normalizer. Its actual H-orbit spans the quotient and is singular for the
square form. Noncommutativity makes the associated polar nonzero.

The proof retains the literal subgroup embeddings and quotient action;
no central quotient or fixed summand is discarded. This supplies the
common orbit input to the normal Bender and index-five source branches.

Source: Aschbacher–Smith 14.2.6, 14.2.16 and 14.2.20, pp.982, 985–987.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
variable {G : Type*} [Group G] [Finite G]

open ChapterG.Section02

noncomputable def closureActor (D : Setup G) : D.H →* MulAut D.U :=
  D.U.normalizerMonoidHom.comp
    (inclusion (show D.H ≤ normalizer (D.U : Set G) from
      le_normalizer_conjugateSpanBy D.V D.H))

omit [Finite G] in
theorem closureActor_apply (D : Setup G) (g : D.H) (u : D.U) :
    (closureActor D g u : G) = g.val * u.val * g.val⁻¹ := rfl

noncomputable def frattiniActor (D : Setup G) :
    D.H →* MulAut (D.U ⧸ frattini D.U) :=
  (quotientAut (frattini D.U)).comp (closureActor D)

noncomputable def frattiniRepresentation (D : Setup G)
    (htwo : IsPGroup 2 D.U) :
    letI := SmallFrattini.quotientElementary htwo
    Representation (ZMod 2) D.H (Additive (D.U ⧸ frattini D.U)) := by
  let := SmallFrattini.quotientElementary htwo
  exact Representation.elementaryRepresentation (p := 2) (frattiniActor D)

theorem frattini_eq_point (D : Setup G) (h : D.Hypothesis)
    (hpoint : Nat.card D.V₁ = 2) (hne : ¬ IsMulCommutative D.U) :
    (frattini D.U).map D.U.subtype = D.V₁ := by
  let : Fact (IsPGroup 2 D.U) := ⟨h.U_isPGroup⟩
  have hphi : frattini D.U ≠ ⊥ := by
    intro hb
    exact hne ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hb).1
  have hcphi : 2 ≤ Nat.card (frattini D.U) := by
    have hh := (frattini D.U).one_lt_card_iff_ne_bot.mpr hphi
    omega
  apply eq_of_le_of_card_ge h.frattini_U_le_point
  rw [card_map_of_injective D.U.subtype_injective,hpoint]
  exact hcphi

theorem frattini_card_two (D : Setup G) (h : D.Hypothesis)
    (hpoint : Nat.card D.V₁ = 2) (hne : ¬ IsMulCommutative D.U) :
    Nat.card (frattini D.U) = 2 := by
  have hh := congrArg (fun A : Subgroup G => Nat.card A) (frattini_eq_point D h hpoint hne)
  simpa only [card_map_of_injective D.U.subtype_injective,hpoint] using hh

private theorem seed_image_card (D : Setup G) (h : D.Hypothesis)
    (hpoint : Nat.card D.V₁ = 2) (hplane : Nat.card D.V = 4)
    (hne : ¬ IsMulCommutative D.U) :
    Nat.card ((QuotientGroup.mk' (frattini D.U)).comp
      (inclusion (le_conjugateSpanBy D.V D.H))).range = 2 := by
  let i : D.V →* D.U := inclusion (le_conjugateSpanBy D.V D.H)
  let f := (QuotientGroup.mk' (frattini D.U)).comp i
  have hphi := frattini_eq_point D h hpoint hne
  have hk : f.ker.map D.V.subtype = D.V₁ := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      have hv' : i v ∈ frattini D.U := (QuotientGroup.eq_one_iff _).mp hv
      exact hphi.le (mem_map_of_mem D.U.subtype hv')
    · intro hx
      obtain ⟨u,hu,he⟩ := hphi.ge hx
      refine mem_map.mpr ⟨⟨x,h.point_le hx⟩,?_,rfl⟩
      change QuotientGroup.mk' (frattini D.U) (i ⟨x,h.point_le hx⟩) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      have he' : i ⟨x,h.point_le hx⟩ = u := Subtype.ext he.symm
      exact he' ▸ hu
  have hkc : Nat.card f.ker = 2 := by
    have hh := congrArg (fun A : Subgroup G => Nat.card A) hk
    simpa only [card_map_of_injective D.V.subtype_injective,hpoint] using hh
  have hh := f.ker.card_mul_index
  rw [index_ker,hkc,hplane] at hh
  change Nat.card f.range = 2
  omega

/-- The original Frattini action has a single nonzero seed fixed by the
normalizer of the plane, and that seed spans the quotient under H. -/
theorem frattini_seed_orbit (D : Setup G) (h : D.Hypothesis)
    (hpoint : Nat.card D.V₁ = 2) (hplane : Nat.card D.V = 4)
    (hne : ¬ IsMulCommutative D.U) :
    letI := SmallFrattini.quotientElementary h.U_isPGroup
    ∃ w : D.U ⧸ frattini D.U, w ≠ 1 ∧
      (∀ v : D.V, QuotientGroup.mk' (frattini D.U)
        (inclusion (le_conjugateSpanBy D.V D.H) v) = 1 ∨
        QuotientGroup.mk' (frattini D.U)
          (inclusion (le_conjugateSpanBy D.V D.H) v) = w) ∧
      (∀ g : D.H, g.val ∈ normalizer (D.V : Set G) →
        frattiniActor D g w = w) ∧
      Submodule.span (ZMod 2) (Set.range (fun g : D.H =>
        frattiniRepresentation D h.U_isPGroup g (Additive.ofMul w))) = ⊤ ∧
      SmallFrattini.quotientQuadraticForm h.U_isPGroup
        (frattini_card_two D h hpoint hne) (Additive.ofMul w) = 0 := by
  let := SmallFrattini.quotientElementary h.U_isPGroup
  let := h.elementary
  let i : D.V →* D.U := inclusion (le_conjugateSpanBy D.V D.H)
  let q := QuotientGroup.mk' (frattini D.U)
  let f := q.comp i
  obtain ⟨w,hw,hunique⟩ := (Nat.card_eq_two_iff' (1:f.range)).mp
    (seed_image_card D h hpoint hplane hne)
  have hw' : (w : D.U ⧸ frattini D.U) ≠ 1 := by
    intro he
    exact hw (Subtype.ext he)
  have hs (v : D.V) : f v = 1 ∨ f v = w.val := by
    by_cases hv : f v = 1
    · exact Or.inl hv
    · exact Or.inr (congrArg Subtype.val (hunique ⟨f v,⟨v,rfl⟩⟩
        (fun he => hv (congrArg Subtype.val he))))
  refine ⟨w.val,hw',hs,?_,?_,?_⟩
  · intro g hg
    have hm : frattiniActor D g w.val ∈ f.range := by
      obtain ⟨v,hv⟩ := w.property
      have hx : g.val*v.val*g.val⁻¹ ∈ D.V :=
        mem_normalizer_iff.mp hg v.val |>.mp v.property
      refine ⟨⟨g.val*v.val*g.val⁻¹,hx⟩,?_⟩
      rw [←hv]
      change QuotientGroup.mk' (frattini D.U) _ = quotientAut (frattini D.U) (closureActor D g) (QuotientGroup.mk' (frattini D.U) (i v))
      rw [quotientAut_apply_mk]
      apply congrArg q
      exact Subtype.ext (closureActor_apply D g (i v)).symm
    have hmne : frattiniActor D g w.val ≠ 1 := by
      intro he
      exact hw' ((frattiniActor D g).map_eq_one_iff.mp he)
    exact congrArg Subtype.val (hunique ⟨_,hm⟩ (fun he => hmne (congrArg Subtype.val he)))
  · exact Representation.conjugateSpan_frattini_orbit_span D.V D.H D.U
      (le_conjugateSpanBy D.V D.H) rfl h.U_isPGroup (closureActor D)
      (closureActor_apply D) w.val hs
  · obtain ⟨v,hv⟩ := w.property
    rw [←hv]
    change SmallFrattini.quotientQuadraticForm h.U_isPGroup
      (frattini_card_two D h hpoint hne) (Additive.ofMul (q (i v))) = 0
    rw [SmallFrattini.quotientQuadraticForm_apply]
    have hsquare : SmallFrattini.quotientSquare h.U_isPGroup
        (frattini_card_two D h hpoint hne) (q (i v)) = 1 := by
      apply Subtype.ext
      change (SmallFrattini.quotientSquare h.U_isPGroup
        (frattini_card_two D h hpoint hne) (QuotientGroup.mk' (frattini D.U) (i v))).val = 1
      rw [SmallFrattini.quotientSquare_apply_mk]
      exact (map_pow i v 2).symm.trans (congrArg i
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 D.V) v) |>.trans i.map_one)
    rw [hsquare,map_one]
    rfl

/-- Noncommutativity is detected by the actual polar on the Frattini quotient. -/
theorem frattini_polar_ne_zero (D : Setup G) (h : D.Hypothesis)
    (hpoint : Nat.card D.V₁ = 2) (hne : ¬ IsMulCommutative D.U) :
    letI := SmallFrattini.quotientElementary h.U_isPGroup
    SmallFrattini.quotientBilinearForm h.U_isPGroup
      (frattini_card_two D h hpoint hne) ≠ 0 := by
  let := SmallFrattini.quotientElementary h.U_isPGroup
  intro hb
  apply hne
  refine ⟨⟨fun x y => ?_⟩⟩
  have hh := congrArg (fun B => B
    (Additive.ofMul (QuotientGroup.mk' (frattini D.U) x))
    (Additive.ofMul (QuotientGroup.mk' (frattini D.U) y))) hb
  rw [SmallFrattini.quotientBilinearForm_apply] at hh
  change SmallFrattini.binaryMark (frattini_card_two D h hpoint hne)
    (SmallFrattini.quotientPolar h.U_isPGroup (frattini_card_two D h hpoint hne)
      (QuotientGroup.mk' (frattini D.U) x) (QuotientGroup.mk' (frattini D.U) y)) = 1 at hh
  have hp := (SmallFrattini.binaryMark (frattini_card_two D h hpoint hne)).map_eq_one_iff.mp hh
  have hc := congrArg Subtype.val hp
  rw [SmallFrattini.quotientPolar_apply_mk] at hc
  exact commutatorElement_eq_one_iff_mul_comm.mp hc

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter12.Section08

/-- The original selected source supplies the literal nonabelian Frattini
space, its singular seed, and its spanning normalizer-fixed orbit. -/
theorem source_frattini_seed_orbit
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H)) :
    let D : Setup G :=
      { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
        T := T, H := H }
    ∃ h : D.Hypothesis,
      (frattini D.U).map D.U.subtype = D.V₁ ∧
      Nat.card (frattini D.U) = 2 ∧
      letI := SmallFrattini.quotientElementary h.U_isPGroup
      ∃ w : D.U ⧸ frattini D.U, w ≠ 1 ∧
        (∀ g : D.H, g.val ∈ normalizer (D.V : Set G) → frattiniActor D g w = w) ∧
        Submodule.span (ZMod 2) (Set.range (fun g : D.H =>
          frattiniRepresentation D h.U_isPGroup g (Additive.ofMul w))) = ⊤ ∧
        SmallFrattini.quotientQuadraticForm h.U_isPGroup
          (frattini_card_two D h
            (plane_centralInvolutions_card T M hM.1.2 hcard e) hne) (Additive.ofMul w) = 0 ∧
        SmallFrattini.quotientBilinearForm h.U_isPGroup
          (frattini_card_two D h
            (plane_centralInvolutions_card T M hM.1.2 hcard e) hne) ≠ 0 := by
  let D : Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨h, _, _⟩ := source_nonabelian_binary_data hG T hempty hM hu hmany hcard e H hH hne
  have hp : Nat.card D.V₁ = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨w,hw,_,hfix,hspan,hzero⟩ := frattini_seed_orbit D h hp hcard hne
  exact ⟨h,frattini_eq_point D h hp hne,frattini_card_two D h hp hne,
    w,hw,hfix,hspan,hzero,frattini_polar_ne_zero D h hp hne⟩

end CFSG.Quasithin.Chapter14.Section02.LocalBinary
