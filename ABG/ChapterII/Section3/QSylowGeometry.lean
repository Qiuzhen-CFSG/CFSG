module
public import ABG.ChapterII.Section2.QDefinitionEquivalence
public import ABG.ChapterII.Section1.SmallSubgroups
public import ABG.ChapterII.Section1.NormalQuaternionCenter
public import ABG.ChapterII.Section1.WreathedNonabelianCenter
public import ABG.ChapterII.Section1.WreathedCentralQuotient
public import ABG.ChapterII.Section1.CentralQuotient
public import ABG.ChapterII.Section1.FourSubgroupCenter
public import Theory.GroupTheory.SubgroupDihedralCentralQuotient

/-!
# Sylow geometry for the enlarged Q-group definition

For any Sylow two-subgroup R of a finite Q-group in the enlarged definition,
its center is cyclic and nontrivial, and its quotient by that actual center
is a dihedral two-group with positive rotation exponent. Every Klein four
subgroup of R meets its center nontrivially. These are the Sylow-geometry
inputs to ABG II.3 Lemma 2, article p24, and the opening of Proposition 3,
article p25. Generalized quaternion and proper wreathed-overgroup cases are
retained; no full-shape hypothesis is added to R.

The defining overgroup witness and Sylow conjugacy give an injective map
from the chosen R whose range X contains the largest quaternion subgroup.
The public noncommutativity theorem records this consequence for every chosen
Sylow subgroup; thus X is noncommutative. In a wreathed overgroup the center of every
noncommutative subgroup maps into the ambient center. In a semidihedral
overgroup, X contains a quaternion subgroup of order eight; its centralizer
is the ambient center of order two, giving the same containment. Both ambient
centers are cyclic and their central quotients are dihedral. The shared
subgroup-quotient theorem then supplies cyclicity and a dihedral model for
X/Z(X). Center nontriviality follows from the finite two-group center theorem.
Actual center and quotient equivalences transport the result back to R.

For the four-subgroup assertion, map the given subgroup into the same
overgroup, apply the established full-shape center-intersection theorem,
and pull the resulting nonidentity central element back through the
injective map. All witnesses use the existing Q definitions and subgroup maps.
-/

/-! Noncommutativity also transfers to every Sylow of an odd-index subgroup:
its injective ambient image is a Sylow of the original Q-group, since both
factors of its index are odd. This supplies the matrix-centralizer input
for the original odd-index constituent in II.3 Proposition 3. -/

namespace ABG
universe u

private theorem quaternion_not_commutative {S : Type*} [Group S]
    (hS : IsGeneralizedQuaternionGroup S) : ¬ IsMulCommutative S := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hS
  have hc : Nat.card (Subgroup.center S) = 2 :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans
      (QuaternionGroup.card_center_of_two_le (2 ^ n)
        (by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn))
  intro hcomm
  rw [Subgroup.center_eq_top_iff.mpr hcomm, Subgroup.card_top,
    Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card] at hc
  have : 0 < 2 ^ n := by positivity
  omega

private theorem exists_embedding
    {G : Type u} [Group G] [Finite G] (hG : IsQGroup G) (R : Sylow 2 G) :
    ∃ (S : Type u) (iS : Group S), letI := iS;
      (Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) ∧
        ∃ (f : R →* S) (Y : Subgroup S), Function.Injective f ∧
          IsLargestQuaternionSubgroup Y ∧ Y ≤ f.range := by
  obtain ⟨S, iS, hS, R₀, f, Y, K, hf, hY, _, _, _, _, hlink⟩ :=
    isQGroup_iff_quaternionOvergroup.mp hG
  let : Group S := iS
  let e : R ≃* R₀ := Sylow.equiv R R₀
  refine ⟨S, iS, hS, f.comp e.toMonoidHom, Y, hf.comp e.injective, hY, ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← hlink]
  exact Subgroup.map_mono le_top

private theorem center_le_of_semidihedral_largest
    {S : Type*} [Group S] [Finite S] (hS : Stellmacher.IsSemidihedralGroup S)
    (Y X : Subgroup S) (hY : IsLargestQuaternionSubgroup Y) (hYX : Y ≤ X) :
    (Subgroup.center X).map X.subtype ≤ Subgroup.center S := by
  obtain ⟨Y₀, hY₀, _, hmax⟩ := QuasiDihedral.exists_largest_quaternion hS
  have heY : Y₀ = Y := (hY.2 Y₀ hY₀).2
    (le_antisymm (hY.2 Y₀ hY₀).1 (Subgroup.card_le_of_le (hmax Y hY.1)))
  obtain ⟨_, Q, _, hQ, _, _, hlocal⟩ := QuasiDihedral.four_quaternion_subgroups hS
  have hQY : Q ≤ Y := heY ▸ hmax Q ⟨1, by omega, by simpa using hQ⟩
  have hCQ := (hlocal Q (Or.inr hQ)).1
  have hCQcard : Nat.card (Subgroup.centralizer (Q : Set S)) = 2 := by
    rw [hCQ, Subgroup.card_map_of_injective Q.subtype_injective]
    obtain ⟨eQ⟩ := hQ
    exact (Nat.card_congr (Subgroup.centerCongr eQ).toEquiv).trans
      (QuaternionGroup.card_center_of_two_le 2 (by omega))
  have heC : Subgroup.center S = Subgroup.centralizer (Q : Set S) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.center_le_centralizer _)
      (by rw [QuasiDihedral.card_center hS, hCQcard])
  rw [heC]
  rintro x ⟨x, hx, rfl⟩ y hy
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hYX (hQY hy)⟩)

/-- Every Sylow two-subgroup of an enlarged Q-group is noncommutative. -/
public theorem qGroup_sylow_not_isMulCommutative
    {G : Type u} [Group G] [Finite G] (hG : IsQGroup G) (R : Sylow 2 G) :
    ¬ IsMulCommutative R := by
  obtain ⟨S, iS, _, f, Y, hf, hY, hYX⟩ := exists_embedding hG R
  let : Group S := iS
  let X := f.range
  let e : R ≃* X := MonoidHom.ofInjective hf
  intro hc
  have hXc : IsMulCommutative X := ⟨⟨fun a b => e.symm.injective (by
    rw [map_mul, map_mul]
    exact hc.is_comm.comm _ _)⟩⟩
  let := hXc
  have hYc : IsMulCommutative Y := by
    apply IsMulCommutative.of_comm
    intro a b
    exact Subtype.ext (congrArg (fun x : X => (x : S)) (mul_comm'
      (⟨a, hYX a.property⟩ : X) (⟨b, hYX b.property⟩ : X)))
  exact quaternion_not_commutative hY.1 hYc

/-- Every chosen Sylow subgroup of an enlarged Q-group has the source center and quotient geometry. -/
public theorem qGroup_sylow_center_quotient_geometry
    {G : Type u} [Group G] [Finite G] (hG : IsQGroup G) (R : Sylow 2 G) :
    IsCyclic (Subgroup.center R) ∧ Nontrivial (Subgroup.center R) ∧
      ∃ n : ℕ, 1 ≤ n ∧ Nonempty ((R ⧸ Subgroup.center R) ≃* DihedralGroup (2 ^ n)) := by
  obtain ⟨S, iS, hS, f, Y, hf, hY, hYX⟩ := exists_embedding hG R
  let : Group S := iS
  let X := f.range
  let e : R ≃* X := MonoidHom.ofInjective hf
  have hXnc : ¬ IsMulCommutative X := by
    intro hc
    apply qGroup_sylow_not_isMulCommutative hG R
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hc.is_comm.comm _ _)⟩⟩
  have hgeo : IsCyclic (Subgroup.center X) ∧ ∃ n : ℕ, 1 ≤ n ∧
      Nonempty ((X ⧸ Subgroup.center X) ≃* DihedralGroup (2 ^ n)) := by
    rcases hS with hS | ⟨n, hS⟩
    · obtain ⟨n, hn, hcard, a, b, ha, hb, hab, hg⟩ := hS
      let : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
      let : IsCyclic (Subgroup.center S) :=
        isCyclic_of_prime_card (QuasiDihedral.card_center ⟨n, hn, hcard, a, b, ha, hb, hab, hg⟩)
      obtain ⟨ed⟩ := QuasiDihedral.central_quotient_equiv hn hcard a b ha hb hab hg
      exact Subgroup.exists_dihedral_center_quotient_of_center_le ed X hXnc
        (center_le_of_semidihedral_largest ⟨n, hn, hcard, a, b, ha, hb, hab, hg⟩ Y X hY hYX)
    · obtain ⟨P⟩ := Wreathed.nonempty_presentation hS
      let : IsCyclic (Subgroup.center S) := P.center_cyclic
      exact Subgroup.exists_dihedral_center_quotient_of_center_le P.central_quotient_equiv.some
        X hXnc (P.nonabelian_center_le X hXnc)
  let : IsCyclic (Subgroup.center X) := hgeo.1
  have hRnc : ¬ IsMulCommutative R := by
    intro hc
    let := hc
    apply hXnc
    apply IsMulCommutative.of_comm
    intro a b
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    exact (e.map_mul a b).symm.trans ((congrArg e (mul_comm' a b)).trans (e.map_mul b a))
  have hRne : Nontrivial R := by
    by_contra hn
    have := not_nontrivial_iff_subsingleton.mp hn
    exact hRnc inferInstance
  let := hRne
  refine ⟨isCyclic_of_injective (Subgroup.centerCongr e).toMonoidHom
    (Subgroup.centerCongr e).injective, R.isPGroup'.center_nontrivial, ?_⟩
  obtain ⟨n, hn, ⟨ed⟩⟩ := hgeo.2
  have hc : (Subgroup.center R).map e.toMonoidHom = Subgroup.center X := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr e ⟨x, hx⟩).property
    · intro hx
      exact ⟨e.symm x, (Subgroup.centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
  exact ⟨n, hn, ⟨(QuotientGroup.congr _ _ e hc).trans ed⟩⟩

/-- A Klein four subgroup of an enlarged Q-group Sylow subgroup meets its center nontrivially. -/
public theorem qGroup_four_subgroup_inf_center_ne_bot
    {G : Type u} [Group G] [Finite G] (hG : IsQGroup G) (R : Sylow 2 G)
    (V : Subgroup R) (hV : IsKleinFour V) : V ⊓ Subgroup.center R ≠ ⊥ := by
  obtain ⟨S, iS, hS, f, _, hf, _, _⟩ := exists_embedding hG R
  let : Group S := iS
  let e : V ≃* V.map f := V.equivMapOfInjective f hf
  have hW : IsKleinFour (V.map f) :=
    ⟨(Nat.card_congr e.symm.toEquiv).trans hV.card_four,
      (Monoid.exponent_eq_of_mulEquiv e.symm).trans hV.exponent_two⟩
  have hne := four_subgroup_inf_center_ne_bot hS (V.map f) hW
  intro hbot
  apply hne
  apply le_antisymm _ bot_le
  rintro x ⟨⟨v, hv, rfl⟩, hc⟩
  have hvc : v ∈ Subgroup.center R := by
    apply Subgroup.mem_center_iff.mpr
    intro r
    apply hf
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hc (f r)
  have hvone : v = 1 := Subgroup.mem_bot.mp (hbot ▸ ⟨hv, hvc⟩)
  simpa only [hvone, map_one] using (Subgroup.one_mem (⊥ : Subgroup S))

/-- Every Sylow two-subgroup in an odd-index subgroup of a Q-group is noncommutative. -/
public theorem qGroup_odd_index_sylow_not_isMulCommutative
    {H : Type*} [Group H] [Finite H] (hH : IsQGroup H)
    (L : Subgroup H) (hL : Odd L.index) (S : Sylow 2 L) :
    ¬ IsMulCommutative S := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Sylow 2 H := (S.isPGroup'.map L.subtype).toSylow (by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two S.not_dvd_index
      hL.not_two_dvd_nat)
  let e : S ≃* T := (S : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective
  intro hS
  apply qGroup_sylow_not_isMulCommutative hH T
  exact ⟨⟨fun a b => e.symm.injective (by
    rw [map_mul, map_mul]
    exact hS.is_comm.comm _ _)⟩⟩

end ABG
