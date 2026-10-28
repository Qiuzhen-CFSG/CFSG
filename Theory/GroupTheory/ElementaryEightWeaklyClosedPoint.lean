module

public import Theory.GroupTheory.ElementaryEightSolvableCore

/-!
# A weakly closed point in an elementary-eight automizer

Let a solvable automorphism group of an elementary abelian group of order
eight contain a two-element subgroup with fixed plane W. Suppose an orbit
meets W only at its starting point z, moves z, and the stabilizer of two
distinct nonidentity points z and a is trivial. Then the automorphism group
is isomorphic to the symmetric group on three letters.

The orbit has odd size at most five; its size divides 168, so it has size
three. Its permutation image contains an involution and is all of S3.
The stabilizer of z injects into the six points different from 1 and z,
giving group order at most eighteen. Divisibility by 168 leaves orders six
and twelve. In the latter case the solvable two-core has order at least
four, but its image in S3 is trivial and the action kernel has order two.
This contradiction proves faithfulness of the three-point action.

This source-neutral counting argument supplies the quotient assertion in
Parrott, *A characterization of the Tits' simple group* (1972), p.676.
-/

open Subgroup MulAction

private theorem orbit_three
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 8) (A B : Subgroup (MulAut V)) (hBA : B ≤ A)
    (hB : Nat.card B = 2) (W : Subgroup V) (hW : Nat.card W = 4)
    (z : V) (hzW : z ∈ W)
    (hfix : ∀ v : V, (∀ b ∈ B, b v = v) ↔ v ∈ W)
    (hinter : ∀ v ∈ orbit A z, v ∈ W → v = z)
    (hmove : ∃ g : A, g • z ≠ z) : Nat.card (orbit A z) = 3 := by
  classical
  let O := orbit A z
  let T := B.subgroupOf A
  have hT : Nat.card T = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv).trans hB
  have hTp : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by simpa using hT)
  let zO : O := ⟨z, mem_orbit_self z⟩
  have hfixed : fixedPoints T O = {zO} := by
    ext v
    constructor
    · intro hv
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      apply hinter v v.property
      apply (hfix v).mp
      intro b hb
      have hh := hv (⟨⟨b, hBA hb⟩, hb⟩ : T)
      exact congrArg Subtype.val hh
    · rintro rfl t
      apply Subtype.ext
      exact (hfix z).mpr hzW t.val.val t.property
  have hfixedcard : Nat.card (fixedPoints T O) = 1 := by
    change (fixedPoints T O).ncard = 1
    rw [hfixed, Set.ncard_singleton]
  have hmod := hTp.card_modEq_card_fixedPoints O
  rw [hfixedcard] at hmod
  have hupper : Nat.card O ≤ 5 := by
    have hsub : O ⊆ insert z (W : Set V)ᶜ := by
      intro v hv
      by_cases hvW : v ∈ W
      · exact Or.inl (hinter v hv hvW)
      · exact Or.inr hvW
    have hh := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem (by simpa using hzW), Set.ncard_compl] at hh
    change Nat.card O ≤ Nat.card V - Nat.card W + 1 at hh
    omega
  have hnot1 : Nat.card O ≠ 1 := by
    intro hO
    have : Subsingleton O := Finite.card_le_one_iff_subsingleton.mp (by omega)
    obtain ⟨g, hg⟩ := hmove
    exact hg (congrArg Subtype.val (Subsingleton.elim (g • zO) zO))
  have hdiv : Nat.card O ∣ 168 := by
    have hh := Nat.card_congr (orbitProdStabilizerEquivGroup A z)
    rw [Nat.card_prod] at hh
    apply dvd_trans (Dvd.intro _ hh)
    have hAut := card_mulAut_of_elementary_eight V hV
    exact hAut ▸ A.card_subgroup_dvd_card
  have hnot5 : Nat.card O ≠ 5 := by
    intro h5
    norm_num [h5] at hdiv
  change Nat.card O % 2 = 1 % 2 at hmod
  change Nat.card O = 3
  omega

private theorem normal_two_perm_three_eq_bot
    (P : Subgroup (Equiv.Perm (Fin 3))) [P.Normal] (hP : IsPGroup 2 P) : P = ⊥ := by
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hdiv : Nat.card P ∣ 6 := hperm ▸ P.card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card P) 3 := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hdiv2 : Nat.card P ∣ 2 := hcop.dvd_mul_right.mp hdiv
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv2 with h1 | h2
  · exact Subgroup.card_eq_one.mp h1
  · have hc := central_of_normal_card_two P h2
    have hh : ∀ x : Equiv.Perm (Fin 3), (∀ y, y * x = x * y) → x = 1 := by
      decide +kernel
    apply le_antisymm _ bot_le
    intro x hx
    exact hh x (mem_center_iff.mp (hc hx))

/-- A moving weakly closed point and a trivial two-point stabilizer identify
a solvable elementary-eight automizer with the symmetric group of degree three. -/
public theorem elementaryEight_automizer_equiv_perm_three
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 8) (A : Subgroup (MulAut V)) [Group.IsSolvable A]
    (B : Subgroup (MulAut V)) (hBA : B ≤ A) (hB : Nat.card B = 2)
    (W : Subgroup V) (hW : Nat.card W = 4) (z a : V)
    (hz1 : z ≠ 1) (ha1 : a ≠ 1) (haz : a ≠ z) (hzW : z ∈ W)
    (hfix : ∀ v : V, (∀ b ∈ B, b v = v) ↔ v ∈ W)
    (hinter : ∀ v ∈ orbit A z, v ∈ W → v = z)
    (hmove : ∃ g : A, g • z ≠ z)
    (hpair : ∀ g ∈ A, g z = z → g a = a → g = 1) :
    Nonempty (A ≃* Equiv.Perm (Fin 3)) := by
  classical
  let O := orbit A z
  have hO : Nat.card O = 3 := orbit_three hV A B hBA hB W hW z hzW hfix hinter hmove
  let e : O ≃ Fin 3 := (Finite.equivFin O).trans (finCongr hO)
  let ψ : A →* Equiv.Perm O := MulAction.toPermHom A O
  let φ : A →* Equiv.Perm (Fin 3) := (Equiv.permCongrHom e).toMonoidHom.comp ψ
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hφker (g : A) : φ g = 1 ↔ ∀ v : O, g • v = v := by
    change (Equiv.permCongrHom e) (ψ g) = 1 ↔ _
    rw [map_eq_one_iff (Equiv.permCongrHom e) (Equiv.permCongrHom e).injective]
    exact Equiv.ext_iff
  let T := B.subgroupOf A
  have hT : Nat.card T = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv).trans hB
  have hTnot : ¬ T ≤ φ.ker := by
    intro hTker
    obtain ⟨g, hg⟩ := hmove
    have hvW : g • z ∈ W := by
      apply (hfix (g • z)).mp
      intro b hb
      let t : A := ⟨b, hBA hb⟩
      have ht : φ t = 1 := MonoidHom.mem_ker.mp (hTker (show t ∈ T from hb))
      exact congrArg Subtype.val ((hφker t).mp ht ⟨g • z, mem_orbit z g⟩)
    exact hg (hinter _ (mem_orbit z g) hvW)
  have himage2 : Nat.card (T.map φ) = 2 := by
    have hdiv : Nat.card (T.map φ) ∣ 2 := hT ▸ T.card_map_dvd φ
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
    · exact (hTnot ((map_eq_bot_iff T).mp (Subgroup.card_eq_one.mp h1))).elim
    · exact h2
  have htwo : 2 ∣ Nat.card φ.range := himage2 ▸ card_dvd_of_le (map_le_range φ T)
  let zO : O := ⟨z, mem_orbit_self z⟩
  have hrangege : 3 ≤ Nat.card φ.range := by
    have hsurj : Function.Surjective (fun g : φ.range => e.symm (g.val (e zO))) := by
      intro v
      obtain ⟨g, hg⟩ := mem_orbit_iff.mp v.property
      refine ⟨φ.rangeRestrict g, ?_⟩
      apply Subtype.ext
      change (e.symm ((Equiv.permCongrHom e) (ψ g) (e zO)) : V) = v.val
      change (e.symm (e ((ψ g) (e.symm (e zO)))) : V) = v.val
      simp only [Equiv.symm_apply_apply]
      change g • z = v.val
      exact hg
    simpa only [hO] using Nat.card_le_card_of_surjective _ hsurj
  have hrangedvd : Nat.card φ.range ∣ 6 := hperm ▸ φ.range.card_subgroup_dvd_card
  have hrange : Nat.card φ.range = 6 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hrangedvd
    interval_cases hn : Nat.card φ.range <;> norm_num at *
  have hsurj : Function.Surjective φ := by
    apply MonoidHom.range_eq_top.mp
    exact eq_top_of_card_eq _ (hrange.trans hperm.symm)
  have hstab : Nat.card (stabilizer A z) ≤ 6 := by
    let X : Set V := ({1, z} : Set V)ᶜ
    have hX : Nat.card X = 6 := by
      change X.ncard = 6
      rw [Set.ncard_compl, Set.ncard_pair hz1.symm, hV]
    let evaluation : stabilizer A z → X := fun g =>
      ⟨(g.val.val : MulAut V) a, by
        change (g.val.val : MulAut V) a ∉ ({1, z} : Set V)
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        constructor
        · exact fun hh => ha1 ((g.val.val : MulAut V).injective (hh.trans (map_one _).symm))
        · intro hh
          have hg : (g.val.val : MulAut V) z = z := g.property
          exact haz ((g.val.val : MulAut V).injective (hh.trans hg.symm))⟩
    have hinj : Function.Injective evaluation := by
      intro g k hgk
      have hga : (g.val.val : MulAut V) a = (k.val.val : MulAut V) a :=
        congrArg Subtype.val hgk
      have hgz : (g.val.val : MulAut V) z = z := g.property
      have hkz : (k.val.val : MulAut V) z = z := k.property
      have heq : (k.val.val : MulAut V)⁻¹ * g.val.val = 1 := by
        apply hpair _ (A.mul_mem (A.inv_mem k.val.property) g.val.property)
        · change (k.val.val : MulAut V)⁻¹ ((g.val.val : MulAut V) z) = z
          rw [hgz]
          exact ((congrArg (fun v => (k.val.val : MulAut V)⁻¹ v) hkz).symm.trans
            ((k.val.val : MulAut V).symm_apply_apply z))
        · change (k.val.val : MulAut V)⁻¹ ((g.val.val : MulAut V) a) = a
          rw [hga]
          exact (k.val.val : MulAut V).symm_apply_apply a
      apply Subtype.ext
      apply Subtype.ext
      exact (inv_mul_eq_one.mp heq).symm
    exact (Nat.card_le_card_of_injective evaluation hinj).trans_eq hX
  have hAupper : Nat.card A ≤ 18 := by
    have hh := Nat.card_congr (orbitProdStabilizerEquivGroup A z)
    rw [Nat.card_prod, hO] at hh
    omega
  have hprod : Nat.card φ.ker * 6 = Nat.card A := by
    have hh := φ.ker.card_mul_index
    rw [index_ker, hrange] at hh
    exact hh
  have hAdvd : Nat.card A ∣ 168 :=
    (card_mulAut_of_elementary_eight V hV) ▸ A.card_subgroup_dvd_card
  have hAcases : Nat.card A = 6 ∨ Nat.card A = 12 := by
    have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
    have hkbound : Nat.card φ.ker ≤ 3 := by omega
    have hnot18 : Nat.card A ≠ 18 := by
      intro hh
      norm_num [hh] at hAdvd
    omega
  have hA : Nat.card A = 6 := by
    rcases hAcases with hh | hh
    · exact hh
    · have hcore := four_le_card_pCore_of_solvable_elementary_eight_automorphisms V hV A
        (by rw [hh]; decide)
      let P := (pCore 2 A).map φ
      let : P.Normal := (inferInstance : (pCore 2 A).Normal).map φ hsurj
      have hP : P = ⊥ := normal_two_perm_three_eq_bot P (pCore_isPGroup.map φ)
      have hle : pCore 2 A ≤ φ.ker := (Subgroup.map_eq_bot_iff _).mp hP
      have hc := card_le_of_le hle
      omega
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp
    (Subgroup.card_eq_one.mp (by omega))
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩
