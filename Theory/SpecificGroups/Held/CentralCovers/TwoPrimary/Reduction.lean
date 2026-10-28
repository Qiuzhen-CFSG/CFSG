module
public import Theory.GroupTheory.PerfectCentralCover
public import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.Tactic

/-!
# Reduction to prime-order central kernels

If a prime divides the kernel of a finite perfect central cover, first quotient
by a complement to its Sylow subgroup in the central kernel. Then quotient by
a maximal subgroup of the remaining primary kernel. Perfectness survives both
quotients, and the resulting central cover has kernel of order exactly that
prime. In particular, excluding double covers proves that every such kernel
has odd order; no splitting assertion for arbitrary central extensions is used.

The primary quotient construction adapts the existing proof in
`Theory.Alternating.Reduction`, `exists_pPrimary_quotient_central_extension`,
with only the general group-theory imports needed here. The order-prime step
uses `Theory.PGroup.card_quotient_coatom_eq_prime`.

Application: Aschbacher–Smith, I.1.1 and I.1.3, printed p.407. The calculation
for the Held model is a separate obligation.
-/

namespace PerfectCentralCovering.PrimaryReduction
universe u v

/-- Cardinality of the image of a subgroup under a quotient, expressed as
the index of the induced kernel. -/
private theorem card_map_eq_index
    {H Q : Type*} [Group H] [Finite H] [Group Q]
    (K : Subgroup H) (U : Subgroup K) (q : H →* Q)
    (hker : q.ker.subgroupOf K = U) :
    Nat.card (K.map q) = U.index := by
  let r := q.subgroupMap K
  have hrker : r.ker = U := by
    rw [show r = q.subgroupMap K by rfl, Subgroup.ker_subgroupMap, hker]
  calc
    Nat.card (K.map q) = Nat.card r.range := by
      rw [MonoidHom.range_eq_top.mpr (q.subgroupMap_surjective K), Subgroup.card_top]
    _ = r.ker.index := (Subgroup.index_ker r).symm
    _ = U.index := by rw [hrker]

/-- A surjective homomorphism sends a central subgroup into the center. -/
private theorem map_le_center
    {H Q : Type*} [Group H] [Group Q]
    (q : H →* Q) (hq : Function.Surjective q)
    {K : Subgroup H} (hK : K ≤ Subgroup.center H) :
    K.map q ≤ Subgroup.center Q := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨a, rfl⟩ := hq y
  rw [← map_mul, ← map_mul]
  exact congrArg q (Subgroup.mem_center_iff.mp (hK hx) a)

/-- Isolate a prescribed primary part of a central extension kernel.  If a
prime `p` divides the kernel of a finite perfect central extension, quotient
by a Schur--Zassenhaus complement to a Sylow `p`-subgroup of the kernel.  The
result is again a surjective central extension, now with a nontrivial
`p`-group kernel. -/
public theorem exists_primary_quotient
    {H G : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Group G] [Finite G]
    {p : Nat} [Fact p.Prime]
    (f : H →* G) (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hpker : p ∣ Nat.card f.ker) :
    ∃ (X : Subgroup H) (_ : X.Normal)
      (fbar : (H ⧸ X) →* G),
      X ≤ f.ker ∧
      Function.Surjective fbar ∧
      fbar.ker ≤ Subgroup.center (H ⧸ X) ∧
      IsPGroup p fbar.ker ∧ p ∣ Nat.card fbar.ker := by
  let K := f.ker
  let : CommGroup (Subgroup.center H) := {
    mul_comm := fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp a.2 b.1).symm }
  let j : K →* Subgroup.center H :=
    K.subtype.codRestrict (Subgroup.center H) (fun x => hker x.2)
  let : CommGroup K := j.commGroupOfInjective (by
    intro a b hab
    dsimp [j] at hab
    apply Subtype.ext
    exact congrArg (fun z : Subgroup.center H => (z : H)) hab)
  let P : Sylow p K := default
  let : (P : Subgroup K).Normal := inferInstance
  obtain ⟨C, hPC⟩ :=
    Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
  let X : Subgroup H := C.map K.subtype
  have hXker : X ≤ f.ker := by
    rintro x ⟨c, hc, rfl⟩
    exact c.2
  have hXcenter : X ≤ Subgroup.center H := hXker.trans hker
  let hXnormal : X.Normal := ⟨fun x hx a => by
    simpa [Subgroup.mem_center_iff.mp (hXcenter hx) a] using hx⟩
  let : X.Normal := hXnormal
  let q : H →* H ⧸ X := QuotientGroup.mk' X
  let fbar : (H ⧸ X) →* G := QuotientGroup.lift X f hXker
  have hqker : q.ker.subgroupOf K = C := by
    rw [show q = QuotientGroup.mk' X by rfl, QuotientGroup.ker_mk']
    change Subgroup.comap K.subtype (C.map K.subtype) = C
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective C
  have hfbarCard : Nat.card fbar.ker = Nat.card P := by
    rw [show fbar = QuotientGroup.lift X f hXker by rfl,
      QuotientGroup.ker_lift]
    exact (card_map_eq_index K C q hqker).trans
      hPC.index_eq_card
  have hfbarSurj : Function.Surjective fbar :=
    QuotientGroup.lift_surjective_of_surjective X f hsurj hXker
  have hfbarCenter : fbar.ker ≤ Subgroup.center (H ⧸ X) := by
    rw [show fbar = QuotientGroup.lift X f hXker by rfl,
      QuotientGroup.ker_lift]
    exact map_le_center q
      (QuotientGroup.mk'_surjective X) hker
  have hfbarP : IsPGroup p fbar.ker := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    apply IsPGroup.of_card
    rw [hfbarCard, hk]
  have hpbar : p ∣ Nat.card fbar.ker := by
    rw [hfbarCard]
    exact P.dvd_card_of_dvd_card hpker
  exact ⟨X, hXnormal, fbar, hXker, hfbarSurj, hfbarCenter, hfbarP, hpbar⟩


/-- A nontrivial primary central kernel has a central quotient of prime order. -/
public theorem exists_prime_order_quotient
    {H : Type u} {G : Type v} [Group H] [Finite H] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (f : Cover H G)
    (hdiv : p ∣ Nat.card f.toMonoidHom.ker) :
    ∃ (Y : Type u) (_ : Group Y) (_ : Finite Y),
      ∃ g : Cover Y G, Nat.card g.toMonoidHom.ker = p := by
  let := f.isPerfect
  obtain ⟨N, hN, fbar, _, hsurj, hcenter, hprimary, hdivbar⟩ :=
    exists_primary_quotient f.toMonoidHom f.surjective f.ker_le_center hdiv
  let := hN
  let K := fbar.ker
  let : Fact (IsPGroup p K) := ⟨hprimary⟩
  have hcard : Nat.card K ≠ 1 := by
    intro h
    exact (Fact.out : p.Prime).not_dvd_one (h ▸ hdivbar)
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_le_of_ne Nat.card_pos (Ne.symm hcard))
  obtain ⟨U, hU, _⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Subgroup K)).resolve_left bot_ne_top
  have hindex : U.index = p := by
    let : U.Normal := coatom_normal_of_isPGroup (p := p) hU
    exact card_quotient_coatom_eq_prime (p := p) hU
  let R := U.map K.subtype
  have hRK : R ≤ fbar.ker := Subgroup.map_subtype_le U
  have hRZ : R ≤ Subgroup.center (H ⧸ N) := hRK.trans hcenter
  let : R.Normal := ⟨fun x hx a => by
    simpa [Subgroup.mem_center_iff.mp (hRZ hx) a] using hx⟩
  let q := QuotientGroup.mk' R
  let g : Cover ((H ⧸ N) ⧸ R) G := {
    toMonoidHom := QuotientGroup.lift R fbar hRK
    surjective := QuotientGroup.lift_surjective_of_surjective R fbar hsurj hRK
    isPerfect := inferInstance
    ker_le_center := by
      rw [QuotientGroup.ker_lift]
      exact map_le_center q (QuotientGroup.mk'_surjective R) hcenter }
  refine ⟨_, inferInstance, inferInstance, g, ?_⟩
  change Nat.card (QuotientGroup.lift R fbar hRK).ker = p
  rw [QuotientGroup.ker_lift]
  have hqker : q.ker.subgroupOf K = U := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective U
  exact (card_map_eq_index K U q hqker).trans hindex

/-- It suffices to exclude central covers whose kernels have order two.
The arbitrary odd part and higher powers of two are removed by central quotients. -/
public theorem odd_card_kernel_of_no_double_cover
    {H : Type u} {G : Type v} [Group H] [Finite H] [Group G] [Finite G]
    (f : Cover H G)
    (hno : ∀ (Y : Type u) [Group Y] [Finite Y] (g : Cover Y G),
      Nat.card g.toMonoidHom.ker ≠ 2) :
    Odd (Nat.card f.toMonoidHom.ker) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨Y, hY, hfin, g, hcard⟩ := exists_prime_order_quotient f heven.two_dvd
  exact hno Y g hcard

end PerfectCentralCovering.PrimaryReduction
