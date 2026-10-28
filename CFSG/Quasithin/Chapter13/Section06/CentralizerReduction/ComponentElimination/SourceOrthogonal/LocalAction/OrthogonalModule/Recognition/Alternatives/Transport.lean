module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Preparation

/-!
# Identifying the iterated B.5.1 section

Apply B.5.1 to the actual upper module U = [W_K,K⁺]. Perfectness implies
[U,K⁺] = U: modulo the second moved space, every displacement defines a
homomorphism from the perfect actor to an abelian group. Inclusion therefore
identifies the two upper spaces, their entire fixed submodules, and their
central quotients. The quotient equivalence intertwines the same K⁺ action.
No central extension is split, and no action is inferred from its dimension.

These transports let all six clauses of the source-correct classification
be used on the literal section from Recognition.Section. Selection of the
orthogonal alternative remains a separate mathematical obligation.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed p.99, and the paragraph following 13.6.23, printed p.933/PDF p.950.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [Group.IsPerfect C]
    (s : MovedSection ρ C)

/-- Perfectness makes the component's moved space its own moved space. -/
theorem upper_moved_eq_top : moved (s.space.toRepresentation.comp C.subtype) ⊤ = ⊤ := by
  let σ := s.space.toRepresentation.comp C.subtype
  let M := moved σ ⊤
  let q := M.mkQ
  have hq (g : C) (u : s.space.toSubmodule) : q (σ g u) = q u := by
    apply (Submodule.Quotient.eq M).mpr
    exact Submodule.subset_span ⟨g, mem_top _, u, Submodule.mem_top, rfl⟩
  let δ (v : V) (g : C) : s.space.toSubmodule :=
    ⟨ρ g v - v, s.space_eq.symm ▸
      Submodule.subset_span ⟨g, g.property, v, Submodule.mem_top, rfl⟩⟩
  have hd (v : V) (g h : C) : δ v (g * h) = σ g (δ v h) + δ v g := by
    apply Subtype.ext
    change ρ ((g : D) * h) v - v = ρ g (ρ h v - v) + (ρ g v - v)
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel
  have hz (v : V) (g : C) : q (δ v g) = 0 := by
    let f : C →* Multiplicative (s.space.toSubmodule ⧸ M) :=
      { toFun g := Multiplicative.ofAdd (q (δ v g))
        map_one' := by
          change q (δ v 1) = 0
          have he : δ v 1 = 0 := by
            apply Subtype.ext
            change ρ (1 : D) v - v = 0
            simp
          rw [he, map_zero]
        map_mul' g h := by
          change q (δ v (g * h)) = q (δ v g) + q (δ v h)
          rw [hd, map_add, hq, add_comm] }
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    exact congrArg (fun x : f.range => Multiplicative.toAdd x.val)
      (Subsingleton.elim (⟨f g, g, rfl⟩ : f.range) 1)
  have hall (v : V) (hv : v ∈ moved ρ C) :
      q ⟨v, s.space_eq.symm ▸ hv⟩ = 0 := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, hg, w, _, rfl⟩ := hv
      exact hz w ⟨g, hg⟩
    | zero => exact map_zero q
    | add x y hx hy ihx ihy =>
      change q (⟨x, s.space_eq.symm ▸ hx⟩ + ⟨y, s.space_eq.symm ▸ hy⟩) = 0
      rw [map_add, ihx, ihy, add_zero]
    | smul c x hx ih =>
      change q (c • ⟨x, s.space_eq.symm ▸ hx⟩) = 0
      rw [map_smul, ih, smul_zero]
  apply top_unique
  intro u _
  exact (Submodule.Quotient.mk_eq_zero M).mp (hall u (s.space_eq ▸ u.property))

variable (t : MovedSection (s.space.toRepresentation.comp C.subtype) ⊤)

/-- The iterated B.5.1 upper space is literally all of the original upper space. -/
theorem iterated_space_eq_top : t.space.toSubmodule = ⊤ :=
  t.space_eq.trans (upper_moved_eq_top ρ C s)

/-- Inclusion, with its inverse supplied by perfectness. -/
noncomputable def iteratedUpperEquiv : t.space.toSubmodule ≃ₗ[ZMod 2] s.space.toSubmodule where
  toFun u := u.val
  invFun u := ⟨u, (iterated_space_eq_top ρ C s t).symm ▸ Submodule.mem_top⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem iteratedUpperEquiv_intertwines (g : C) (u : t.space.toSubmodule) :
    iteratedUpperEquiv ρ C s t (t.space.toRepresentation g u) =
      s.space.toRepresentation (g : D) (iteratedUpperEquiv ρ C s t u) := rfl

/-- Inclusion identifies the complete fixed spaces, including any central kernel. -/
theorem iteratedUpperEquiv_map_central :
    t.central.toSubmodule.map (iteratedUpperEquiv ρ C s t).toLinearMap = s.central.toSubmodule := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [s.central_eq]
    intro g
    have hg := (t.central_eq ▸ hw) ⟨g, mem_top _⟩
    exact congrArg Subtype.val hg
  · intro hu
    let w := (iteratedUpperEquiv ρ C s t).symm u
    refine ⟨w, ?_, (iteratedUpperEquiv ρ C s t).apply_symm_apply u⟩
    rw [t.central_eq]
    intro g
    apply Subtype.ext
    exact (s.central_eq ▸ hu) g.val

/-- The induced equivalence uses the quotient of the actual inclusion. -/
noncomputable def iteratedCentralEquiv :
    (t.space.toSubmodule ⧸ t.central.toSubmodule) ≃ₗ[ZMod 2]
      (s.space.toSubmodule ⧸ s.central.toSubmodule) :=
  Submodule.Quotient.equiv _ _ (iteratedUpperEquiv ρ C s t)
    (iteratedUpperEquiv_map_central ρ C s t)

theorem iteratedCentralEquiv_mk (u : t.space.toSubmodule) :
    iteratedCentralEquiv ρ C s t (t.central.toSubmodule.mkQ u) =
      s.central.toSubmodule.mkQ u.val := rfl

theorem iteratedCentralEquiv_intertwines (g : C)
    (u : t.space.toSubmodule ⧸ t.central.toSubmodule) :
    iteratedCentralEquiv ρ C s t ((t.action) g u) =
      (s.action) (g : D) (iteratedCentralEquiv ρ C s t u) := by
  induction u using Submodule.Quotient.induction_on with
  | _ w => rfl

/-- The actor is unchanged by the iterated central quotient. -/
noncomputable def iteratedActionEquiv : ActionEquiv t.action (s.action.comp C.subtype) where
  groupEquiv := MulEquiv.refl _
  linearEquiv := iteratedCentralEquiv ρ C s t
  intertwines := iteratedCentralEquiv_intertwines ρ C s t

variable {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W}

/-- Transport upper-space coordinates without changing either group marking. -/
noncomputable def upperCoordinates_of_iterated
    (e : ActionEquiv (t.space.toRepresentation.comp (⊤ : Subgroup C).subtype) σ) :
    ActionEquiv (s.space.toRepresentation.comp C.subtype) σ where
  groupEquiv := Subgroup.topEquiv.symm.trans e.groupEquiv
  linearEquiv := (iteratedUpperEquiv ρ C s t).symm.trans e.linearEquiv
  intertwines g u := e.intertwines (Subgroup.topEquiv.symm g)
    ((iteratedUpperEquiv ρ C s t).symm u)

/-- Transport central-quotient coordinates through the actual inclusion. -/
noncomputable def quotientCoordinates_of_iterated
    (e : ActionEquiv (t.action.comp (⊤ : Subgroup C).subtype) σ) :
    ActionEquiv (s.action.comp C.subtype) σ where
  groupEquiv := Subgroup.topEquiv.symm.trans e.groupEquiv
  linearEquiv := (iteratedCentralEquiv ρ C s t).symm.trans e.linearEquiv
  intertwines g u := by
    change e.linearEquiv ((iteratedCentralEquiv ρ C s t).symm ((s.action) (g : D) u)) = _
    have he : (iteratedCentralEquiv ρ C s t).symm ((s.action) (g : D) u) =
        (t.action) g ((iteratedCentralEquiv ρ C s t).symm u) := by
      apply (iteratedCentralEquiv ρ C s t).injective
      rw [LinearEquiv.apply_symm_apply, iteratedCentralEquiv_intertwines,
        LinearEquiv.apply_symm_apply]
    rw [he]
    exact e.intertwines (Subgroup.topEquiv.symm g) _

/-- A selected row on the iterated section gives the same actual natural action. -/
theorem natural_of_iterated_natural (n : ℕ)
    (h : IsAlternatingNatural (t.action.comp (⊤ : Subgroup C).subtype) n) :
    IsAlternatingNatural (s.action.comp C.subtype) n := by
  obtain ⟨e⟩ := h
  exact ⟨quotientCoordinates_of_iterated ρ C s t e⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives
