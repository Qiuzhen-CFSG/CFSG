module
public import ABG.ChapterII.Section1.WreathedDefs

/-!
# A chosen wreathed presentation

The presentation and named elements/subgroups of ABG Chapter II §1, preceding
Lemma 2 (article p.9). The exact cardinality and height bound are retained,
so later normal-form arguments can establish independence of the generators.
The definitions expose the chosen generators for the thirteen structural
clauses; existence merely repackages `IsWreathedOfHeight`.
-/

namespace ABG.Wreathed

variable (S : Type*) [Group S] (n : ℕ)

/-- A choice of the three generators in the defining wreathed presentation. -/
public structure Presentation where
  height : 2 ≤ n
  card : Nat.card S = 2 ^ (2 * n + 1)
  s : S
  t : S
  z : S
  s_pow : s ^ (2 ^ n) = 1
  t_pow : t ^ (2 ^ n) = 1
  z_sq : z ^ 2 = 1
  conj_s : z⁻¹ * s * z = t
  conj_t : z⁻¹ * t * z = s
  commute : s * t = t * s
  generate : Subgroup.closure ({s, t, z} : Set S) = ⊤

variable {S n}

public theorem nonempty_presentation (h : ABG.IsWreathedOfHeight S n) :
    Nonempty (Presentation S n) := by
  rcases h with ⟨hn, hc, s, t, z, hs, ht, hz, hzs, hzt, hst, hgen⟩
  exact ⟨⟨hn, hc, s, t, z, hs, ht, hz, hzs, hzt, hst, hgen⟩⟩

namespace Presentation

variable (P : Presentation S n)

@[expose] public def u : S := P.s * P.t
@[expose] public def r : S := P.s * P.t⁻¹
@[expose] public def x : S := P.u ^ (2 ^ (n - 1))
@[expose] public def x₂ : S := P.s ^ (2 ^ (n - 1))
@[expose] public def x₃ : S := P.t ^ (2 ^ (n - 1))
@[expose] public def d : S := P.x₂ * P.z
@[expose] public def U : Subgroup S := Subgroup.closure ({P.s, P.t} : Set S)
@[expose] public def T : Subgroup S := Subgroup.closure ({P.x, P.x₂, P.x₃} : Set S)
@[expose] public def T₀ : Subgroup S := Subgroup.closure ({P.x, P.z} : Set S)
@[expose] public def Y : Subgroup S := Subgroup.closure ({P.r, P.d} : Set S)

end Presentation
end ABG.Wreathed
