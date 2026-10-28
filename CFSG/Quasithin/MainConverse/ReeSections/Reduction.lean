module

public import CFSG.Quasithin.MainConverse.RankOneSections.Linear
public import CFSG.Quasithin.MainConverse.SuzukiSections
public import CFSG.Quasithin.MainConverse.ExceptionalSections.Reduction
public import Theory.SpecificGroups.ReeF4.Model
public import Theory.GroupTheory.CoreFreeMaximalQuotient
public import Theory.GroupTheory.SimpleSectionSolvableLayers
public import Mathlib.Order.Atoms.Finite

/-!
# Subfield induction for the proper sections of the large Ree groups

The required source statement is condition K of Aschbacher--Smith,
Theorem 0.1.2(1), printed pp.4 and 482: every simple quotient of every
subgroup of a proper subgroup must be a known concrete group.

Malle's maximal-subgroup theorem has two parabolic families, solvable
torus normalizers, SU₃ and PGU₃ extensions, a Suzuki wreath product, a
symplectic extension, and proper Ree subfield groups. `Envelope` records
the actual group constructions needed for this argument, including normal
extensions, rather than assigning unconnected family tags. The subfield
degree divides `2*m+1` and is strictly smaller. At degree one the full
Ree group must be treated through its derived Tits subgroup.

The elementary assembly below removes solvable layers, uses the proved
linear and Suzuki section calculations, and inducts on the field exponent.
A core-free maximal subgroup handles a noninjective quotient of the whole
Ree group. Thus this reduction does not demand simplicity of every smaller
Ree model. It leaves the actual subgroup exhaustion, core-free subgroup,
derived-endpoint comparison, and unitary/symplectic/Tits section calculations
explicit. It is not the completed source proper-K theorem.

Sources: G. Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139
(1991), 52--69, DOI 10.1016/0021-8693(91)90283-E; the list is also reproduced
in the proof of Theorem 5 of Himstedt--Nguyen--Tiep,
*On the restriction of cross characteristic representations of ²F₄(q) to
proper subgroups*, arXiv:0910.4758, pp.2--3. We use field size
`q = 2^(2*m+1)`, as in the latter reference.
-/

@[expose] public section

namespace CFSG.Quasithin.MainConverse.ReeSections

open CFSG.KnownSimple
open Theory.GroupTheory

universe u v

/-- Concrete carriers, with the large Ree family added to the existing partial
exceptional catalogue. This is a list of possible outputs, not an exhaustion
assertion. The latter catalogue is also the output of the Tits section task. -/
inductive IsSectionCarrier (S : Type u) [Group S] : Prop
  | known (h : ExceptionalSections.IsSectionCarrier S)
  | ree (h : ReeF4.IsReeF4Model S)

theorem IsSectionCarrier.of_mulEquiv {S : Type u} {T : Type v} [Group S] [Group T]
    (h : IsSectionCarrier T) (e : S ≃* T) : IsSectionCarrier S := by
  cases h with
  | known h => exact .known (h.of_mulEquiv e)
  | ree h => exact .ree (h.of_mulEquiv e)

/-- The structural leaves in the Ree maximal-subgroup argument. Each recursive
Ree leaf retains the exact subfield degree restriction, including `k = 0`. -/
inductive Envelope (m : ℕ) : (H : Type) → [Group H] → Prop where
  | solvable (H : Type) [Group H] (hH : Group.IsSolvable H) : Envelope m H
  | linearTwo (H : Type) [Group H] (q : ℕ)
      (hH : ClassicalGroup.IsPSL H 2 q) : Envelope m H
  | suzuki (k : ℕ) (hk : 1 ≤ k) :
      Envelope m (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup k)
  | unitaryThree (H : Type) [Group H]
      (hH : ClassicalGroup.IsPSU H 3 (2 ^ (2 * m + 1))) : Envelope m H
  | symplecticFour (H : Type) [Group H]
      (hH : ClassicalGroup.IsPSp H 2 (2 ^ (2 * m + 1))) : Envelope m H
  | tits : Envelope m Tits.ParrottGroup
  | reeSubfield (k : ℕ) (hlt : k < m) (hdiv : (2 * k + 1) ∣ (2 * m + 1)) :
      Envelope m (ReeF4.Model k)
  | subgroup {H L : Type} [Group H] [Group L] (i : H →* L)
      (hi : Function.Injective i) (hL : Envelope m L) : Envelope m H
  | quotient {H L : Type} [Group H] [Group L] (p : L →* H)
      (hp : Function.Surjective p) (hL : Envelope m L) : Envelope m H
  | extension {H : Type} [Group H] (N : Subgroup H) [N.Normal]
      (hN : Envelope m N) (hQ : Envelope m (H ⧸ N)) : Envelope m H

/-- Solvable inner and outer layers preserve the structural envelope. -/
theorem Envelope.of_solvableLayers {m : ℕ} {H L : Type} [Group H] [Group L]
    (h : SolvableLayersEmbedding H L) (hL : Envelope m L) : Envelope m H := by
  obtain ⟨N, hN, hQ, R, hR, hsolv, j, hj⟩ := h
  let := hN
  let := hR
  exact .extension N (.extension R (.solvable _ hsolv) (.subgroup j hj hL))
    (.solvable _ hQ)

/-- Interpret an envelope using smaller Ree groups and the three independent
section calculations. Linear and Suzuki leaves are discharged here. -/
theorem Envelope.isKGroup {m : ℕ} {H : Type} [Group H] (h : Envelope m H)
    (hU : ∀ (L : Type) [Group L], ClassicalGroup.IsPSU L 3 (2 ^ (2 * m + 1)) →
      IsKGroup IsConstructedCarrier L)
    (hSp : ∀ (L : Type) [Group L], ClassicalGroup.IsPSp L 2 (2 ^ (2 * m + 1)) →
      IsKGroup IsConstructedCarrier L)
    (hT : IsKGroup ExceptionalSections.IsSectionCarrier Tits.ParrottGroup)
    (hRee : ∀ k, k < m → (2 * k + 1) ∣ (2 * m + 1) →
      IsKGroup IsSectionCarrier (ReeF4.Model k)) : IsKGroup IsSectionCarrier H := by
  induction h with
  | solvable H hs =>
      let := hs
      exact (solvable_isKGroup_constructed H).mono (fun _ _ h => .known (.constructed h))
  | linearTwo H q hH =>
      exact (psl2_isKGroup_constructed hH).mono (fun _ _ h => .known (.constructed h))
  | suzuki k hk =>
      exact (suzuki_isKGroup_constructed hk (MulEquiv.refl _)).mono
        (fun _ _ h => .known (.constructed h))
  | unitaryThree H hH => exact (hU H hH).mono (fun _ _ h => .known (.constructed h))
  | symplecticFour H hH => exact (hSp H hH).mono (fun _ _ h => .known (.constructed h))
  | tits => exact hT.mono (fun _ _ => .known)
  | reeSubfield k hlt hdiv => exact hRee k hlt hdiv
  | subgroup i hi _ ih => exact ih.of_injective i hi
  | quotient p hp _ ih => exact ih.of_surjective p hp
  | extension N _ _ ihN ihQ => exact IsKGroup.of_normal_quotient N ihN ihQ

/-- Structural exhaustion to be established from the actual Ree matrices.
This definition does not assume that the envelopes have known sections. -/
def MaximalSubgroupCover : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (ReeF4.Model m), IsCoatom M → Envelope m M

/-- The nonlocal part of Malle's theorem, separate from the parabolic
calculations. This predicate asserts no known-simple section conclusion. -/
def NonlocalMaximalCover : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (ReeF4.Model m), IsCoatom M →
    ¬ IsTwoLocal M → Envelope m M

/-- Combine the independent local and nonlocal structural calculations. -/
theorem maximalSubgroupCover_of_local_and_nonlocal
    (hlocal : ∀ m, 1 ≤ m → ∀ M : Subgroup (ReeF4.Model m), IsCoatom M →
      IsTwoLocal M → Envelope m M)
    (hnonlocal : NonlocalMaximalCover) : MaximalSubgroupCover := by
  intro m hm M hM
  by_cases h : IsTwoLocal M
  · exact hlocal m hm M hM h
  · exact hnonlocal m hm M hM h

/-- The full degree-one Ree group is handled by its derived subgroup;
the commutator quotient is automatically solvable. -/
theorem zero_isKGroup_of_derived_equiv
    (e : commutator (ReeF4.Model 0) ≃* Tits.ParrottGroup)
    (hT : IsKGroup ExceptionalSections.IsSectionCarrier Tits.ParrottGroup) :
    IsKGroup IsSectionCarrier (ReeF4.Model 0) := by
  refine IsKGroup.of_normal_quotient (K := IsSectionCarrier)
    (commutator (ReeF4.Model 0)) ?_ ?_
  · exact (hT.of_injective e.toMonoidHom e.injective).mono (fun _ _ => .known)
  · let : IsMulCommutative (ReeF4.Model 0 ⧸ commutator (ReeF4.Model 0)) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
    let : Group.IsSolvable (ReeF4.Model 0 ⧸ commutator (ReeF4.Model 0)) :=
      Group.isSolvable_of_comm (fun _ _ => mul_comm' _ _)
    exact (solvable_isKGroup_constructed _).mono (fun _ _ h => .known (.constructed h))

/-- Strong induction closes the whole-group and proper-subgroup cases together.
All intrinsic Ree and independent-family premises remain explicit. -/
theorem model_isKGroup_of_inputs
    (hcover : MaximalSubgroupCover)
    (hcore : ∀ m, 1 ≤ m → ∃ P : Subgroup (ReeF4.Model m),
      IsCoatom P ∧ P.normalCore = ⊥)
    (hzero : Nonempty (commutator (ReeF4.Model 0) ≃* Tits.ParrottGroup))
    (hU : ∀ m, 1 ≤ m → ∀ (L : Type) [Group L],
      ClassicalGroup.IsPSU L 3 (2 ^ (2 * m + 1)) → IsKGroup IsConstructedCarrier L)
    (hSp : ∀ m, 1 ≤ m → ∀ (L : Type) [Group L],
      ClassicalGroup.IsPSp L 2 (2 ^ (2 * m + 1)) → IsKGroup IsConstructedCarrier L)
    (hT : IsKGroup ExceptionalSections.IsSectionCarrier Tits.ParrottGroup)
    (m : ℕ) : IsKGroup IsSectionCarrier (ReeF4.Model m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm : m = 0
      · subst m
        exact zero_isKGroup_of_derived_equiv hzero.some hT
      have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hproper : ∀ U : Subgroup (ReeF4.Model m), U ≠ ⊤ →
          IsKGroup IsSectionCarrier U := by
        intro U hUne
        obtain ⟨M, hM, hUM⟩ := (eq_top_or_exists_le_coatom U).resolve_left hUne
        exact ((hcover m hm M hM).isKGroup (hU m hm) (hSp m hm) hT
          (fun k hk _ => ih k hk)).of_injective
            (Subgroup.inclusion hUM) (Subgroup.inclusion_injective hUM)
      intro S _ hs U f hf
      let := hs
      by_cases hU : U = ⊤
      · subst U
        let g : ReeF4.Model m →* S := f.comp Subgroup.topEquiv.symm.toMonoidHom
        have hg : Function.Surjective g := hf.comp Subgroup.topEquiv.symm.surjective
        by_cases hinj : Function.Injective g
        · exact .ree ⟨m, hm, ⟨(MulEquiv.ofBijective g ⟨hinj, hg⟩).symm⟩⟩
        · obtain ⟨P, hP, hcoreP⟩ := hcore m hm
          have hsurj := P.surjective_domRestrict_of_coatom_normalCore_eq_bot
            hP hcoreP g hg hinj
          let a : (⊤ : Subgroup P) ≃* P := Subgroup.topEquiv
          exact hproper P hP.ne_top S hs ⊤
            ((g.domRestrict P).comp a.toMonoidHom) (hsurj.comp a.surjective)
      · let a : (⊤ : Subgroup U) ≃* U := Subgroup.topEquiv
        exact hproper U hU S hs ⊤ (f.comp a.toMonoidHom) (hf.comp a.surjective)

/-- Transport the concrete section calculation to groups and simple targets
in any universe, using the actual quotient by the section map's kernel. -/
theorem section_isKGroup_of_injective {G : Type u} {H : Type v}
    [Group G] [Group H] (hH : IsKGroup IsSectionCarrier H)
    (i : G →* H) (hi : Function.Injective i) : IsKGroup IsSectionCarrier G := by
  intro S _ hs U f hf
  let := hs
  let a := Subgroup.equivMapOfInjective U i hi
  let g : U.map i →* S := f.comp a.symm.toMonoidHom
  have hg : Function.Surjective g := hf.comp a.symm.surjective
  let e := QuotientGroup.quotientKerEquivOfSurjective g hg
  let : IsSimpleGroup (U.map i ⧸ g.ker) := e.isSimpleGroup
  exact (hH _ inferInstance (U.map i) (QuotientGroup.mk' g.ker)
    (QuotientGroup.mk'_surjective g.ker)).of_mulEquiv e.symm

end CFSG.Quasithin.MainConverse.ReeSections
