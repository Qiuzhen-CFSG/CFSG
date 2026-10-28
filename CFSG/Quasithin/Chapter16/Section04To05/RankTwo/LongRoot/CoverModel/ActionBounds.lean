module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.SevenAction
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.GroupTheory.CharacteristicRestrictionInnerSquares
public import Theory.Frattini.PGroup
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupAction.Invariant

/-!
# Seven-free actions on the two intrinsic residual sections

Automorphisms trivial on X/O₂(X) centralize the conjugation action of X on
O₂(X)/Φ(O₂(X)). The top action is seven-free when its quotient is actually
isomorphic to A₅, since Aut(A₅) is S₅.

On a 256-element group a fixed-free automorphism of order five has a
seven-free centralizer: the fixed subgroup of a commuting seven-automorphism
has power-of-two order congruent to 256 modulo seven and to one modulo five.
Only order 256 is possible. A variant permits order dividing 512 and at most
two five-fixed points; seven fixes those points, and the same congruences
again force the whole group to be fixed.

The variant applies to a section epimorphism with kernel of order dividing
two onto the natural 256-element module. It does not require the covering
kernel to lie in the Frattini subgroup. All sections and action maps below
are literal. These are conditional reductions; the G₂ cover's section
comparison and its five-element must still be constructed.

Source: Aschbacher–Smith, Lemma 16.5.13, printed p.1202. The counting proof
replaces the full endomorphism-ring computation for the two image bounds.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.CoverModel

private theorem fixed_card_mod_prime {E : Type*} [Group E] [Finite E]
    (p : ℕ) [Fact p.Prime] (a : MulAut E) (ha : a ^ p = 1) :
    Nat.card E % p = Nat.card a.fixedSubgroup % p := by
  let A := zpowers a
  have hp : IsPGroup p A := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [A, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha)
  have heq : FixedPoints.subgroup A E = a.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup a x).mpr (hx ⟨a, mem_zpowers a⟩)
    · intro hx b
      have hle : A ≤ MulAction.stabilizer (MulAut E) x :=
        zpowers_le.mpr ((MulAut.mem_fixedSubgroup a x).mp hx)
      exact hle b.property
  have hmod := hp.card_modEq_card_fixedPoints E
  change Nat.card E % p = Nat.card (FixedPoints.subgroup A E) % p at hmod
  rwa [heq] at hmod

/-- An order-seven automorphism commuting with a fixed-free five-action on
256 elements is trivial. Only fixed-point counting is needed. -/
theorem seven_automorphism_eq_one {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E = 256) (a b : MulAut E) (ha : a ^ 5 = 1)
    (hfree : ∀ x : E, a x = x → x = 1)
    (hb : b ^ 7 = 1) (hab : Commute a b) : b = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let A := zpowers a
  let D := b.fixedSubgroup
  have hcomm (c : A) (x : E) : b ((c : MulAut E) x) = (c : MulAut E) (b x) := by
    have hc : Commute b (c : MulAut E) := by
      obtain ⟨n, hn⟩ := c.property
      rw [← hn]
      exact hab.symm.zpow_right n
    exact congrArg (fun f : MulAut E => f x) hc.eq
  let : IsInvariant A E D := ⟨by
    intro c x
    simp only [D, MulAut.mem_fixedSubgroup]
    change b x = x ↔ b ((c : MulAut E) x) = (c : MulAut E) x
    rw [hcomm]
    exact (c : MulAut E).injective.eq_iff.symm⟩
  have hbot : FixedPoints.subgroup A D = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply hfree
    exact congrArg Subtype.val (hx ⟨a, mem_zpowers a⟩)
  have hp : IsPGroup 5 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [A, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha)
  have hmod5 := hp.card_modEq_card_fixedPoints D
  change Nat.card D % 5 = Nat.card (FixedPoints.subgroup A D) % 5 at hmod5
  rw [hbot, card_bot] at hmod5
  have hmod7 := fixed_card_mod_prime 7 b hb
  rw [hE] at hmod7
  have hdiv : Nat.card D ∣ 2 ^ 8 := by
    simpa [hE] using D.card_subgroup_dvd_card
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hfull : Nat.card D = 256 := by
    change 256 % 7 = Nat.card D % 7 at hmod7
    interval_cases n
    all_goals simp_all
  have htop : D = ⊤ := D.eq_top_of_card_eq (hfull.trans hE.symm)
  apply MulEquiv.ext
  intro x
  exact (MulAut.mem_fixedSubgroup b x).mp (show x ∈ D from htop ▸ mem_top x)

private theorem small_two_divisors_eq {m n : ℕ}
    (hm : m ∣ 512) (hn : n ∣ 512) (h5 : m % 5 = n % 5)
    (h7 : m % 7 = n % 7) : m = n := by
  have hm' := Nat.mem_divisors.mpr ⟨hm, by decide⟩
  have hn' := Nat.mem_divisors.mpr ⟨hn, by decide⟩
  rw [show (512 : ℕ).divisors = {1, 2, 4, 8, 16, 32, 64, 128, 256, 512} by decide] at hm' hn'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm' hn'
  omega

/-- A central two-fold extension may leave one trivial dimension in its
Frattini section. The same counting argument still excludes seven. -/
theorem seven_automorphism_eq_one_of_small_fixed
    {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E ∣ 512) (a b : MulAut E) (ha : a ^ 5 = 1)
    (hsmall : Nat.card a.fixedSubgroup ≤ 2)
    (hb : b ^ 7 = 1) (hab : Commute a b) : b = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let A := zpowers a
  let B := zpowers b
  let D := b.fixedSubgroup
  let F := a.fixedSubgroup
  have hinv {c d : MulAut E} (hcd : Commute c d) :
      IsInvariant (zpowers c) E d.fixedSubgroup := ⟨by
    rintro ⟨k, hk⟩ x
    have he : d (k x) = k (d x) := by
      obtain ⟨n, rfl⟩ := hk
      exact congrArg (fun f : MulAut E => f x) (hcd.symm.zpow_right n).eq
    simp only [MulAut.mem_fixedSubgroup]
    change d x = x ↔ d (k x) = k x
    rw [he]
    exact k.injective.eq_iff.symm⟩
  let : IsInvariant B E F := hinv hab.symm
  let : IsInvariant A E D := hinv hab
  have hB : IsPGroup 7 B := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [B, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hb)
  have hBFmod := hB.card_modEq_card_fixedPoints F
  change Nat.card F % 7 = Nat.card (FixedPoints.subgroup B F) % 7 at hBFmod
  have hBFle := (FixedPoints.subgroup B F).card_le_card_group
  have hBFtop : FixedPoints.subgroup B F = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by change Nat.card F ≤ 2 at hsmall; omega)
  have hFD : F ≤ D := by
    intro x hx
    have hh : (⟨x, hx⟩ : F) ∈ FixedPoints.subgroup B F := hBFtop ▸ mem_top _
    apply (MulAut.mem_fixedSubgroup b x).mpr
    exact congrArg Subtype.val (hh ⟨b, mem_zpowers b⟩)
  have hcommon : (FixedPoints.subgroup A D).map D.subtype = F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply (MulAut.mem_fixedSubgroup a _).mpr
      exact congrArg Subtype.val (hy ⟨a, mem_zpowers a⟩)
    · intro hx
      refine ⟨⟨x, hFD hx⟩, ?_, rfl⟩
      intro c
      apply Subtype.ext
      exact (show A ≤ MulAction.stabilizer (MulAut E) x from
        zpowers_le.mpr ((MulAut.mem_fixedSubgroup a x).mp hx)) c.property
  have hcommoncard : Nat.card (FixedPoints.subgroup A D) = Nat.card F := by
    rw [← hcommon, card_map_of_injective D.subtype_injective]
  have hA : IsPGroup 5 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [A, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha)
  have hmod5D := hA.card_modEq_card_fixedPoints D
  change Nat.card D % 5 = Nat.card (FixedPoints.subgroup A D) % 5 at hmod5D
  rw [hcommoncard] at hmod5D
  have hmod5 := fixed_card_mod_prime 5 a ha
  have hmod7 := fixed_card_mod_prime 7 b hb
  have hD : Nat.card D ∣ 512 := D.card_subgroup_dvd_card.trans hE
  have hfull : Nat.card D = Nat.card E :=
    small_two_divisors_eq hD hE (hmod5D.trans hmod5.symm) hmod7.symm
  have htop : D = ⊤ := D.eq_top_of_card_eq hfull
  apply MulEquiv.ext
  intro x
  exact (MulAut.mem_fixedSubgroup b x).mp (show x ∈ D from htop ▸ mem_top x)

/-- The weakened bound needed before determining whether the central kernel
lies in the Frattini subgroup. -/
theorem seven_coprime_centralizer_of_small_fixed
    {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E ∣ 512) (a : MulAut E) (ha : a ^ 5 = 1)
    (hsmall : Nat.card a.fixedSubgroup ≤ 2) :
    Nat.Coprime 7 (Nat.card (centralizer ({a} : Set (MulAut E)))) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr
  intro hdiv
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer ({a} : Set (MulAut E))) 7 hdiv
  have he : (b : MulAut E) = 1 := seven_automorphism_eq_one_of_small_fixed hE a b ha hsmall
    (by simpa only [← Subgroup.coe_pow, hb, Subgroup.coe_one] using
      congrArg Subtype.val (pow_orderOf_eq_one b))
    (mem_centralizer_iff.mp b.property a (Set.mem_singleton a))
  have hb1 : b = 1 := Subtype.ext he
  simp [hb1] at hb

/-- Thus the full module centralizer, and every subgroup of it, is seven-free. -/
theorem seven_coprime_centralizer {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E = 256) (a : MulAut E) (ha : a ^ 5 = 1)
    (hfree : ∀ x : E, a x = x → x = 1) :
    Nat.Coprime 7 (Nat.card (centralizer ({a} : Set (MulAut E)))) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr
  intro hdiv
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer ({a} : Set (MulAut E))) 7 hdiv
  have he : (b : MulAut E) = 1 := seven_automorphism_eq_one hE a b ha hfree
    (by simpa only [← Subgroup.coe_pow, hb, Subgroup.coe_one] using
      congrArg Subtype.val (pow_orderOf_eq_one b))
    (mem_centralizer_iff.mp b.property a (Set.mem_singleton a))
  have hb1 : b = 1 := Subtype.ext he
  simp [hb1] at hb

/-- Conjugation by X on the intrinsic Frattini section of its two-core. -/
def innerSectionAction (X : Type*) [Group X] :
    X →* MulAut (pCore 2 X ⧸ frattini (pCore 2 X)) :=
  (quotientAut (frattini (pCore 2 X))).comp MulAut.conjNormal

/-- Inner conjugation by two-core elements vanishes on its Frattini quotient. -/
theorem core_le_innerSectionAction_ker (X : Type*) [Group X] [Finite X] :
    pCore 2 X ≤ (innerSectionAction X).ker := by
  let Q := pCore 2 X
  let : Fact (IsPGroup 2 Q) := ⟨pCore_isPGroup⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  intro x hx
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro v
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) v
  change quotientAut (frattini Q) (MulAut.conjNormal x)
    (QuotientGroup.mk' (frattini Q) q) = QuotientGroup.mk' (frattini Q) q
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' (frattini Q)
    ((⟨x, hx⟩ : Q) * q * (⟨x, hx⟩ : Q)⁻¹) = QuotientGroup.mk' (frattini Q) q
  rw [map_mul, map_mul, map_inv,
    mul_comm (QuotientGroup.mk' (frattini Q) (⟨x, hx⟩ : Q))
      (QuotientGroup.mk' (frattini Q) q), mul_inv_cancel_right]

/-- The actual X/O₂(X)-module structure on O₂(X)/Φ(O₂(X)). -/
def quotientSectionAction (X : Type*) [Group X] [Finite X] :
    (X ⧸ pCore 2 X) →* MulAut (pCore 2 X ⧸ frattini (pCore 2 X)) :=
  QuotientGroup.lift _ (innerSectionAction X) (core_le_innerSectionAction_ker X)

/-- An automorphism fixing the top quotient centralizes the module action.
No claim that this automorphism itself is trivial is made. -/
theorem kernel_image_le_module_centralizer
    {M X : Type*} [Group M] [Group X] [Finite X] (a : M →* MulAut X) :
    (topAction a).ker.map (sectionAction a) ≤
      centralizer ((innerSectionAction X).range : Set _) := by
  rintro f ⟨m, hm, rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨x, rfl⟩
  have ht := DFunLike.congr_fun (MonoidHom.mem_ker.mp hm)
    (QuotientGroup.mk' (pCore 2 X) x)
  change quotientAut (pCore 2 X) (a m) (QuotientGroup.mk' (pCore 2 X) x) =
    QuotientGroup.mk' (pCore 2 X) x at ht
  rw [quotientAut_apply_mk] at ht
  have he : innerSectionAction X (a m x) = innerSectionAction X x :=
    congrArg (quotientSectionAction X) ht
  have hc := congrArg (quotientAut (frattini (pCore 2 X)))
    (characteristic_conjNormal_equivariant (pCore 2 X) (a m) x)
  simp only [map_mul, map_inv] at hc
  change sectionAction a m * innerSectionAction X x * (sectionAction a m)⁻¹ =
    innerSectionAction X (a m x) at hc
  rw [he] at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

/-- Aut(A₅)=S₅ bounds every induced action on a quotient identified with A₅. -/
theorem seven_coprime_top_of_equiv
    {M X : Type*} [Group M] [Group X] [Finite X] (a : M →* MulAut X)
    (e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) :
    Nat.Coprime 7 (Nat.card (topAction a).range) := by
  have hc : Nat.Coprime 7 (Nat.card (MulAut (X ⧸ pCore 2 X))) := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      ← Nat.card_congr Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  exact hc.coprime_dvd_right (card_subgroup_dvd_card _)

/-- The literal kernel image is seven-free once a natural-module five-element
has been constructed on the literal Frattini section. -/
theorem seven_coprime_kernel_image
    {M X : Type*} [Group M] [Group X] [Finite X] (a : M →* MulAut X)
    (hcard : Nat.card (pCore 2 X ⧸ frattini (pCore 2 X)) = 256)
    (s : X) (hs : (innerSectionAction X s) ^ 5 = 1)
    (hfree : ∀ v, innerSectionAction X s v = v → v = 1) :
    Nat.Coprime 7 (Nat.card ((topAction a).ker.map (sectionAction a))) := by
  apply (seven_coprime_centralizer hcard (innerSectionAction X s) hs hfree).coprime_dvd_right
  apply card_dvd_of_le
  exact (kernel_image_le_module_centralizer a).trans
    (centralizer_le (by intro f hf; rcases hf with rfl; exact ⟨s, rfl⟩))
/-- The kernel image bound allowing one additional trivial binary dimension. -/
theorem seven_coprime_kernel_image_of_small_fixed
    {M X : Type*} [Group M] [Group X] [Finite X] (a : M →* MulAut X)
    (hcard : Nat.card (pCore 2 X ⧸ frattini (pCore 2 X)) ∣ 512)
    (s : X) (hs : (innerSectionAction X s) ^ 5 = 1)
    (hsmall : Nat.card (innerSectionAction X s).fixedSubgroup ≤ 2) :
    Nat.Coprime 7 (Nat.card ((topAction a).ker.map (sectionAction a))) := by
  apply (seven_coprime_centralizer_of_small_fixed hcard (innerSectionAction X s)
    hs hsmall).coprime_dvd_right
  apply card_dvd_of_le
  exact (kernel_image_le_module_centralizer a).trans
    (centralizer_le (by intro f hf; rcases hf with rfl; exact ⟨s, rfl⟩))

/-- A comparison with a fixed-free 256-element module supplies the weaker
intrinsic bounds, retaining the actual map and its action compatibility. -/
theorem small_fixed_of_section_epimorphism
    {E W : Type*} [Group E] [Group W] [Finite E] [Finite W]
    (f : E →* W) (hf : Function.Surjective f)
    (hker : Nat.card f.ker ∣ 2) (hW : Nat.card W = 256)
    (a : MulAut E) (b : MulAut W)
    (heq : ∀ v, f (a v) = b (f v))
    (hfree : ∀ w, b w = w → w = 1) :
    Nat.card E ∣ 512 ∧ Nat.card a.fixedSubgroup ≤ 2 := by
  have hcard : Nat.card E = Nat.card f.ker * Nat.card W := by
    rw [← f.ker.card_mul_index, index_ker, f.range_eq_top_of_surjective hf, card_top]
  refine ⟨?_, ?_⟩
  · rw [hcard, hW]
    exact Nat.mul_dvd_mul hker (dvd_refl 256)
  · let j : a.fixedSubgroup →* f.ker := a.fixedSubgroup.subtype.codRestrict _ (by
      intro x
      apply MonoidHom.mem_ker.mpr
      apply hfree
      rw [← heq]
      exact congrArg f ((MulAut.mem_fixedSubgroup a x).mp x.property))
    have hj : Function.Injective j := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : f.ker => (z : E)) h
    exact (Nat.card_le_card_of_injective j hj).trans (Nat.le_of_dvd (by decide) hker)

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.CoverModel
