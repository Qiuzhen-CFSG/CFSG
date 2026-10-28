module
public import Theory.GroupTheory.Amalgam.SylowRigidity

/-!
# Transport of the overlap factorization problem

A compatible amalgam isomorphism conjugates middle-group automorphisms and
transports their endpoint extensions. The same three isomorphisms give an
isomorphism between the corresponding twists, so faithfulness transports too.
Thus a calculation on marked concrete subgroups applies to a transported model,
including a model inside an abstract automorphism group.

An automorphism extending to the left endpoint already factors, by taking the
right endpoint and its overlap restriction to be the identity. The consumer is
the M₁₂ branch of `CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity.MathieuTwelve`.
Source context: Aschbacher--Smith, F.1.11--12, printed pp.262--263. These are
formal transport lemmas, independent of the exceptional uniqueness calculation.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.RankTwoAmalgam
variable {L B R L' B' R' : Type*}
  [Group L] [Group B] [Group R] [Group L'] [Group B'] [Group R']

theorem ExtendsAcross.refl (i : B →* L) : ExtendsAcross i (MulEquiv.refl B) :=
  ⟨MulEquiv.refl L, fun _ => rfl⟩

theorem FactorsThrough.of_left {β : RankTwoAmalgam L B R} {d : MulAut B}
    (h : ExtendsAcross β.left d) : FactorsThrough β d := by
  exact ⟨d, MulEquiv.refl B, h, ExtendsAcross.refl β.right, by ext; rfl⟩

/-- Conjugating the overlap automorphism preserves both commuting squares. -/
def Iso.twistRightIso {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (e : Iso α β) (d : MulAut B) :
    Iso (twistRight α d) (twistRight β (MulAut.congr e.middle d)) where
  left := e.left
  middle := e.middle
  right := e.right
  left_commutes := e.left_commutes
  right_commutes b := by
    simpa [twistRight, MulAut.congr_apply] using e.right_commutes (d b)

theorem ExtendsAcross.transport {i : B →* L} {j : B' →* L'}
    (u : B ≃* B') (v : L ≃* L') (h : ∀ b, v (i b) = j (u b))
    {d : MulAut B} (hd : ExtendsAcross i d) :
    ExtendsAcross j (MulAut.congr u d) := by
  obtain ⟨a, ha⟩ := hd
  refine ⟨MulAut.congr v a, ?_⟩
  intro b
  obtain ⟨b, rfl⟩ := u.surjective b
  rw [← h]
  simpa [MulAut.congr_apply, ha] using h (d b)

theorem FactorsThrough.transport {α : RankTwoAmalgam L B R}
    {β : RankTwoAmalgam L' B' R'} (e : Iso α β) {d : MulAut B}
    (hd : FactorsThrough α d) : FactorsThrough β (MulAut.congr e.middle d) := by
  obtain ⟨l, r, hl, hr, rfl⟩ := hd
  refine ⟨MulAut.congr e.middle l, MulAut.congr e.middle r,
    hl.transport e.middle e.left e.left_commutes,
    hr.transport e.middle e.right e.right_commutes, ?_⟩
  ext b
  simp [MulAut.congr_apply]

/-- Transfer a calculation on concrete marked carriers to any isomorphic amalgam. -/
theorem Iso.transport_faithful_factorization
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'} (e : Iso α β)
    (h : ∀ d : MulAut B, Faithful (twistRight α d) → FactorsThrough α d) :
    ∀ d : MulAut B', Faithful (twistRight β d) → FactorsThrough β d := by
  intro d hf
  obtain ⟨c, rfl⟩ := (MulAut.congr e.middle).surjective d
  exact (h c ((e.twistRightIso c).symm.faithful hf)).transport e

end Theory.GroupTheory.RankTwoAmalgam
