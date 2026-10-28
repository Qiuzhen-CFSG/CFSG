module
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# Non-two-group images of symmetric-three groups

Every proper quotient of S₃ is a two-group. Counting the kernel and image
reduces the only possible nontrivial kernel to a normal two-subgroup, which
vanishes by the proved two-core calculation. This retains the actual image
of the supplied homomorphism and is used when passing conjugate pairs to a
marked centralizer quotient in Aschbacher–Smith13.5.21(iv), p.923.
-/
public section
namespace Subgroup
variable {E J : Type*} [Group E] [Finite E] [Group J] [Finite J]

theorem symmetricThree_image_of_not_isPGroup
    (e : E ≃* Equiv.Perm (Fin 3)) (f : E →* J)
    (hn : ¬ IsPGroup 2 f.range) : Nonempty (f.range ≃* Equiv.Perm (Fin 3)) := by
  have hcE : Nat.card E = 6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hd : Nat.card f.range ∣ 6 := hcE ▸ card_range_dvd f
  have hle := Nat.le_of_dvd (by decide : 0<6) hd
  have hpos := Nat.card_pos (α := f.range)
  have hc : Nat.card f.range = 3 ∨ Nat.card f.range = 6 := by
    interval_cases hh : Nat.card f.range
    · exact (hn (IsPGroup.of_card (n := 0) (by simpa using hh))).elim
    · exact (hn (IsPGroup.of_card (n := 1) (by simpa using hh))).elim
    · exact Or.inl rfl
    · norm_num [hh] at hd
    · norm_num [hh] at hd
    · exact Or.inr rfl
  have hm := f.ker.card_mul_index
  rw [index_ker,hcE] at hm
  have hkcard : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 := by
    rcases hc with hc | hc <;> rw [hc] at hm <;> omega
  have hk : IsPGroup 2 f.ker := by
    rcases hkcard with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by simpa using h1)
    · exact IsPGroup.of_card (n := 1) (by simpa using h2)
  have heker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  have hcore : pCore 2 E = ⊥ := by
    have he := ker_eq_twoCore_of_surjective_perm_three e.toMonoidHom e.surjective
      (by rw [heker];exact IsPGroup.of_card (n := 0) (by simp))
    simpa only [heker] using he.symm
  have hlecore : f.ker ≤ pCore 2 E := le_sSup ⟨inferInstance,hk⟩
  have hker : f.ker = ⊥ := bot_unique (hlecore.trans hcore.le)
  exact ⟨(MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff f).mp hker)).symm.trans e⟩

omit [Finite E] in
/-- Passing to an image with a larger kernel preserves a non-two S₃ pair. -/
theorem symmetricThree_range_of_kernel_le {R : Type*} [Group R] [Finite R]
    (f : E →* J) (g : E →* R) (hk : f.ker ≤ g.ker)
    (hs : IsPGroup 2 f.range ∨ Nonempty (f.range ≃* Equiv.Perm (Fin 3)))
    (hn : ¬ IsPGroup 2 g.range) : Nonempty (g.range ≃* Equiv.Perm (Fin 3)) := by
  have hker : f.rangeRestrict.ker ≤ g.rangeRestrict.ker := by
    simpa only [MonoidHom.ker_rangeRestrict] using hk
  let t : f.range →* g.range :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨g.rangeRestrict,hker⟩
  have ht (x : E) : t (f.rangeRestrict x) = g.rangeRestrict x := by
    simp [t]
  have hsurj : Function.Surjective t := by
    intro y
    obtain ⟨x,rfl⟩ := g.rangeRestrict_surjective y
    exact ⟨f.rangeRestrict x,ht x⟩
  rcases hs with hp | heq
  · exact (hn (hp.of_surjective t hsurj)).elim
  · obtain ⟨e⟩ := heq
    have he : t.range ≃* g.range := MulEquiv.ofBijective t.range.subtype
      ⟨Subtype.val_injective,by intro x;obtain ⟨a,rfl⟩ := hsurj x;exact ⟨⟨t a,⟨a,rfl⟩⟩,rfl⟩⟩
    obtain ⟨j⟩ := symmetricThree_image_of_not_isPGroup e t
      (fun hp => hn (hp.of_equiv he))
    exact ⟨he.symm.trans j⟩
end Subgroup
