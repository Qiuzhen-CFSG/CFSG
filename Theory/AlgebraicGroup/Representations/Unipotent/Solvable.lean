module

public import Theory.AlgebraicGroup.Representations.Unipotent.Basic

universe u z

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A group admitting a faithful finite-dimensional representation in which
every operator is unipotent is solvable. -/
public lemma isSolvable_of_injective_unipotent_generalLinearRepresentation
    {Γ V : Type z} [Group Γ]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    (hinjective : Function.Injective ρ)
    (hunipotent : ∀ g : Γ,
      IsNilpotent (((ρ g : LinearMap.GeneralLinearGroup k V) :
        Module.End k V) - 1)) :
    Group.IsSolvable Γ := by
  induction hdim : Module.finrank k V using Nat.strong_induction_on generalizing Γ V with
  | h n ih =>
      let ρlin : Representation k Γ V := (Units.coeHom _).comp ρ
      have hρlin : ∀ g : Γ, IsNilpotent (ρlin g - 1) := hunipotent
      by_cases hV : Nontrivial V
      · let : Nontrivial V := hV
        obtain ⟨x, hx, hfix⟩ :=
          unipotentRepresentation_exists_common_fixed_ne_zero ρlin hρlin
        let W : Submodule k V := k ∙ x
        have hW (g : Γ) : W ≤ W.comap (ρlin g) := by
          intro y hy
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
          change ρlin g (c • x) ∈ W
          rw [LinearMap.map_smul, hfix]
          exact Submodule.smul_mem W c (Submodule.mem_span_singleton_self x)
        let q := ρlin.quotient W hW
        have hqUnipotent : ∀ g : Γ, IsNilpotent (q g - 1) :=
          Representation.isNilpotent_quotient_sub_one ρlin W hW hρlin
        have hdimQ : Module.finrank k (V ⧸ W) < n := by
          have hsum := Submodule.finrank_quotient_add_finrank W
          rw [finrank_span_singleton hx, hdim] at hsum
          omega
        let qGL : Γ →* LinearMap.GeneralLinearGroup k (V ⧸ W) :=
          q.toHomUnits
        have hqGLUnipotent : ∀ g : Γ,
            IsNilpotent (((qGL g : LinearMap.GeneralLinearGroup k (V ⧸ W)) :
              Module.End k (V ⧸ W)) - 1) :=
          hqUnipotent
        let : Group.IsSolvable qGL.range :=
          ih (Module.finrank k (V ⧸ W)) hdimQ qGL.range.subtype
            qGL.range.subtype_injective (fun g => by
              rcases g.property with ⟨a, ha⟩
              change IsNilpotent
                (((g.1 : LinearMap.GeneralLinearGroup k (V ⧸ W)) :
                  Module.End k (V ⧸ W)) - 1)
              rw [← ha]
              exact hqGLUnipotent a) rfl
        have hkerComm (a b : qGL.ker) : a * b = b * a := by
          apply Subtype.ext
          apply hinjective
          apply Units.ext
          apply LinearMap.ext
          intro y
          have haW : ρlin a y - y ∈ W := by
            rw [← Submodule.Quotient.eq W]
            have haUnits : qGL a = 1 := a.property
            have ha : q a = 1 := congrArg Units.val haUnits
            have hay := LinearMap.congr_fun ha (Submodule.Quotient.mk y)
            simpa [q, Representation.quotient] using hay
          have hbW : ρlin b y - y ∈ W := by
            rw [← Submodule.Quotient.eq W]
            have hbUnits : qGL b = 1 := b.property
            have hb : q b = 1 := congrArg Units.val hbUnits
            have hby := LinearMap.congr_fun hb (Submodule.Quotient.mk y)
            simpa [q, Representation.quotient] using hby
          obtain ⟨ca, hca⟩ := Submodule.mem_span_singleton.mp haW
          obtain ⟨cb, hcb⟩ := Submodule.mem_span_singleton.mp hbW
          have haeq : ρlin a y = y + ca • x := by
            calc
              ρlin a y = y + (ρlin a y - y) := by abel
              _ = y + ca • x := by rw [← hca]
          have hbeq : ρlin b y = y + cb • x := by
            calc
              ρlin b y = y + (ρlin b y - y) := by abel
              _ = y + cb • x := by rw [← hcb]
          change ρlin ((a : Γ) * (b : Γ)) y =
            ρlin ((b : Γ) * (a : Γ)) y
          rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
          rw [hbeq, haeq, map_add, map_add, map_smul, map_smul, hfix, hfix]
          rw [haeq, hbeq]
          abel
        let : Group.IsSolvable qGL.ker := Group.isSolvable_of_comm hkerComm
        apply Group.isSolvable_of_ker_le_range qGL.ker.subtype qGL.rangeRestrict
        rw [MonoidHom.ker_rangeRestrict]
        exact fun a ha => ⟨⟨a, ha⟩, rfl⟩
      · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
        let : Subsingleton Γ :=
          ⟨fun a b => hinjective (Subsingleton.elim _ _)⟩
        exact Group.isSolvable_of_top_eq_bot Γ (Subsingleton.elim _ _)

end

end Theory.AlgebraicGroup
