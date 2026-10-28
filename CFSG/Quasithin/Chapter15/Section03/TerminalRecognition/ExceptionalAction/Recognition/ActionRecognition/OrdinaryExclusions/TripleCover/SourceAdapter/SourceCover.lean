module

public import Theory.Representation.HexacodeAction.CoverComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import Theory.GroupTheory.NormalSupplementGluing

/-!
# The source hatted symmetric group is the full hexacode group

The actual symmetric quotient restricts to a central triple covering on
the derived subgroup. Schur uniqueness identifies that restriction over
its prescribed A₆ projection. A lift of a transposition has square in the
cubic kernel. It inverts the kernel and commutes with its own square, so
its square is one. Perfect-central homomorphism rigidity then identifies
its conjugation action with the concrete hexacode lift. Gluing extends
the even equivalence and preserves the full symmetric-coordinate map.

Only the existing `FSource.TripleSymmetric` fields are used. The ambient
SourceInput, offender action and module classification play no role in
this group comparison.

Source: Aschbacher--Smith, A.3.5, F.6.18(8), K.1.3; GLS 3, 5.2.3.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Atlas.Codes
open GLS3.Chapter5.SchurPresentation

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.TripleSymmetric

variable {D : Type*} [Group D]

/-- The literal projection specified by the source triple-symmetric witness. -/
def projection (c : TripleSymmetric D 6) : D →* Equiv.Perm (Fin 6) := by
  let _ := c.normal
  exact c.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' c.kernel)

theorem projection_surjective (c : TripleSymmetric D 6) :
    Function.Surjective (projection c) := by
  let _ := c.normal
  exact c.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective c.kernel)

theorem projection_ker (c : TripleSymmetric D 6) :
    (projection c).ker = c.kernel := by
  let _ := c.normal
  ext g
  change c.quotientEquiv (QuotientGroup.mk' c.kernel g) = 1 ↔ g ∈ c.kernel
  rw [c.quotientEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff g

theorem kernel_card (c : TripleSymmetric D 6) : Nat.card c.kernel = 3 := by
  rw [Nat.card_congr c.kernelEquiv.toEquiv]
  change Nat.card (ZMod 3) = 3
  exact Nat.card_zmod 3

theorem derived_map (c : TripleSymmetric D 6) :
    (commutator D).map (projection c) = alternatingGroup (Fin 6) := by
  rw [map_commutator_eq,
    MonoidHom.range_eq_top.mpr (projection_surjective c),
    ← _root_.commutator_def, alternatingGroup.commutator_perm_eq (by simp)]

/-- The source derived subgroup is the literal inverse image of A₆. -/
theorem mem_derived_iff (c : TripleSymmetric D 6) (g : D) :
    g ∈ commutator D ↔ Equiv.Perm.sign (projection c g) = 1 := by
  constructor
  · intro hg
    have hm : projection c g ∈ (commutator D).map (projection c) :=
      mem_map_of_mem _ hg
    rw [derived_map c] at hm
    exact hm
  · intro hg
    have hm : projection c g ∈ (commutator D).map (projection c) := by
      rw [derived_map c]
      exact hg
    obtain ⟨a, ha, hq⟩ := hm
    have hk : a⁻¹ * g ∈ c.kernel := by
      rw [← projection_ker c]
      change projection c (a⁻¹ * g) = 1
      rw [map_mul, map_inv, hq, inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using
      (commutator D).mul_mem ha (c.kernel_le hk)

/-- The source projection restricted to its actual derived subgroup. -/
def derivedProjection (c : TripleSymmetric D 6) :
    commutator D →* alternatingGroup (Fin 6) where
  toFun x := ⟨projection c x, (mem_derived_iff c x).mp x.property⟩
  map_one' := Subtype.ext (map_one (projection c))
  map_mul' x y := Subtype.ext (map_mul (projection c) (x : D) (y : D))

theorem derivedProjection_surjective (c : TripleSymmetric D 6) :
    Function.Surjective (derivedProjection c) := by
  intro a
  have ha : a.val ∈ (commutator D).map (projection c) := by
    rw [derived_map c]
    exact a.property
  obtain ⟨x, hx, hq⟩ := ha
  exact ⟨⟨x, hx⟩, Subtype.ext hq⟩

theorem mem_derived_center_iff (c : TripleSymmetric D 6) (x : commutator D) :
    x ∈ center (commutator D) ↔ (x : D) ∈ c.kernel := by
  rw [← c.center_eq]
  constructor
  · exact mem_map_of_mem _
  · rintro ⟨y, hy, he⟩
    have hyx : y = x := Subtype.ext he
    change y ∈ (center (commutator D) : Set (commutator D)) at hy
    change x ∈ (center (commutator D) : Set (commutator D))
    exact hyx ▸ hy

theorem derivedProjection_ker (c : TripleSymmetric D 6) :
    (derivedProjection c).ker = center (commutator D) := by
  ext x
  constructor
  · intro hx
    apply (mem_derived_center_iff c x).mpr
    rw [← projection_ker c]
    exact congrArg Subtype.val hx
  · intro hx
    apply Subtype.ext
    change projection c (x : D) = 1
    have hk := (mem_derived_center_iff c x).mp hx
    rwa [← projection_ker c] at hk

theorem derived_isQuasisimple (c : TripleSymmetric D 6) :
    IsQuasisimple (commutator D) where
  toIsPerfect := c.derived.perfect
  simple := by
    obtain ⟨e⟩ := c.derived.quotient
    let _ : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup

theorem derived_center_card (c : TripleSymmetric D 6) :
    Nat.card (center (commutator D)) = 3 := by
  obtain ⟨e⟩ := c.derived.center
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (ZMod 3) = 3
  exact Nat.card_zmod 3

/-- Recognition of the even cover retains its literal coordinate projection. -/
theorem exists_derived_equiv [Finite D] (c : TripleSymmetric D 6) :
    ∃ e : commutator D ≃* HexEvenAutomorphisms,
      hexEvenCoordinate.comp e.toMonoidHom = derivedProjection c := by
  let _ : IsQuasisimple (commutator D) := derived_isQuasisimple c
  let f : Covering (commutator D) (alternatingGroup (Fin 6)) := {
    toMonoidHom := derivedProjection c
    surjective := derivedProjection_surjective c }
  apply Representation.Hexacode.CoverComparison.exists_even_equiv_over_coordinate f
  change Nat.card (derivedProjection c).ker = 3
  rw [derivedProjection_ker c, derived_center_card c]

private theorem signKernel_sup_zpowers
    {G : Type*} [Group G] (χ : G →* ℤˣ) (t : G) (ht : χ t = -1) :
    χ.ker ⊔ zpowers t = ⊤ := by
  apply top_unique
  intro g _
  rcases Int.units_eq_one_or (χ g) with hg | hg
  · exact (show χ.ker ≤ χ.ker ⊔ zpowers t from le_sup_left) hg
  · have hk : g * t⁻¹ ∈ χ.ker := by
      change χ (g * t⁻¹) = 1
      rw [map_mul, map_inv, hg, ht]
      simp
    have hm := (χ.ker ⊔ zpowers t).mul_mem
      ((show χ.ker ≤ χ.ker ⊔ zpowers t from le_sup_left) hk)
      ((show zpowers t ≤ χ.ker ⊔ zpowers t from le_sup_right) (mem_zpowers t))
    simpa only [inv_mul_cancel_right] using hm

private theorem eq_one_or_eq_of_mem_zpowers
    {G : Type*} [Group G] [Finite G] {t x : G}
    (ht : orderOf t = 2) (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ht] at hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hnlt : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

/-- A lift of the fixed adjacent transposition is automatically an involution:
its square is cubic, is inverted by the lift, and commutes with the lift. -/
theorem lift_transposition_sq (c : TripleSymmetric D 6) (t : D)
    (ht : projection c t = hexCoordinateSixHom (hexLift 0)) : t ^ 2 = 1 := by
  let _ := c.normal
  have hodd : Equiv.Perm.sign (projection c t) = -1 := by
    rw [ht]
    exact hexSign_lift 0
  have hhex : (hexLift 0) ^ 2 = 1 := by
    simpa only [pow_two] using hexLift_sq 0
  have hk : t ^ 2 ∈ c.kernel := by
    rw [← projection_ker c]
    change projection c (t ^ 2) = 1
    rw [map_pow, ht, ← map_pow, hhex, map_one]
  let z : c.kernel := ⟨t ^ 2, hk⟩
  have hinv : (z : D) = (z : D)⁻¹ := by
    calc
      (z : D) = t * (z : D) * t⁻¹ := by dsimp [z]; group
      _ = (z : D)⁻¹ := c.inverse_action t hodd z
  have hzinv : z = z⁻¹ := Subtype.ext hinv
  have hz2 : z ^ 2 = 1 := by
    calc
      z ^ 2 = z * z := pow_two z
      _ = z * z⁻¹ := congrArg (fun w => z * w) hzinv
      _ = 1 := mul_inv_cancel z
  have hz3 : z ^ 3 = 1 := by
    have hz := pow_card_eq_one' (x := z)
    rw [kernel_card c] at hz
    exact hz
  have hz1 : z = 1 := by
    have he : z ^ 3 = z := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hz2, one_mul]
    exact he.symm.trans hz3
  exact congrArg Subtype.val hz1

/-- The full source hatted symmetric group is the full hexacode group, with
the original symmetric quotient marking preserved. -/
theorem exists_hexacode_equiv [Finite D] (c : TripleSymmetric D 6) :
    ∃ E : D ≃* HexAutomorphisms,
      hexCoordinateSixHom.comp E.toMonoidHom = projection c := by
  classical
  let _ := c.normal
  let _ : Group.IsPerfect (commutator D) := c.derived.perfect
  obtain ⟨e, he⟩ := exists_derived_equiv c
  have he_point (n : commutator D) :
      hexCoordinateSixHom (e n : HexAutomorphisms) = projection c (n : D) :=
    congrArg Subtype.val (DFunLike.congr_fun he n)
  obtain ⟨t, ht⟩ := projection_surjective c (hexCoordinateSixHom (hexLift 0))
  have ht2 : t ^ 2 = 1 := lift_transposition_sq c t ht
  have htodd : Equiv.Perm.sign (projection c t) = -1 := by
    rw [ht]
    exact hexSign_lift 0
  have htne : t ≠ 1 := by
    intro h
    rw [h, map_one, map_one] at htodd
    norm_num at htodd
  have htorder : orderOf t = 2 := orderOf_eq_prime ht2 htne
  have htout : t ∉ commutator D := by
    intro h
    have hh := (mem_derived_iff c t).mp h
    rw [htodd] at hh
    norm_num at hh
  have hhex2 : (hexLift 0) ^ 2 = 1 := by
    simpa only [pow_two] using hexLift_sq 0
  have hhexne : hexLift 0 ≠ 1 := by
    intro h
    have hh := hexSign_lift 0
    rw [h, map_one] at hh
    norm_num at hh
  have hhexorder : orderOf (hexLift 0) = 2 := orderOf_eq_prime hhex2 hhexne
  let M : Subgroup D := zpowers t
  let tm : M := ⟨t, mem_zpowers t⟩
  have hmgen : ∀ x : M, x ∈ zpowers tm := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, Subtype.ext hn⟩
  have htmorder : orderOf tm = 2 := (Subgroup.orderOf_coe tm).symm.trans htorder
  have hdiv : orderOf (hexLift 0) ∣ orderOf tm := by
    simpa only [hhexorder, htmorder] using (dvd_refl (2 : ℕ))
  let v : M →* HexAutomorphisms := monoidHomOfForallMemZpowers hmgen hdiv
  have hv : v tm = hexLift 0 :=
    monoidHomOfForallMemZpowers_apply_gen hmgen hdiv
  have hvproj : hexCoordinateSixHom.comp v = (projection c).comp M.subtype := by
    apply (MonoidHom.eq_iff_eq_on_generator hmgen _ _).mpr
    change hexCoordinateSixHom (v tm) = projection c t
    rw [hv, ht]
  have hv_point (m : M) : hexCoordinateSixHom (v m) = projection c (m : D) :=
    DFunLike.congr_fun hvproj m
  have hderived : commutator D = (Equiv.Perm.sign.comp (projection c)).ker := by
    ext g
    exact mem_derived_iff c g
  have hgen : commutator D ⊔ M = ⊤ := by
    rw [hderived]
    exact signKernel_sup_zpowers (Equiv.Perm.sign.comp (projection c)) t htodd
  have hgen' : hexSign.ker ⊔ v.range = ⊤ := by
    apply top_unique
    rw [← signKernel_sup_zpowers hexSign (hexLift 0) (hexSign_lift 0)]
    apply sup_le le_sup_left
    apply le_trans _ le_sup_right
    exact zpowers_le.mpr ⟨tm, hv⟩
  have hinter (m : M) : v m ∈ hexSign.ker ↔ (m : D) ∈ commutator D := by
    rw [mem_derived_iff c]
    change Equiv.Perm.sign (hexCoordinateSixHom (v m)) = 1 ↔
      Equiv.Perm.sign (projection c (m : D)) = 1
    rw [hv_point m]
  have hagree (m : M) (hm : (m : D) ∈ commutator D) :
      (e ⟨m, hm⟩ : HexAutomorphisms) = v m := by
    rcases eq_one_or_eq_of_mem_zpowers htorder m.property with hm1 | hmt
    · have hmone : m = 1 := Subtype.ext hm1
      subst m
      simp
    · exact (htout (hmt ▸ hm)).elim
  have hconj (m : M) (n : commutator D) :
      (e (MulAut.conjNormal (m : D) n) : HexAutomorphisms) =
        v m * e n * (v m)⁻¹ := by
    let a : commutator D →* HexEvenAutomorphisms :=
      e.toMonoidHom.comp (MulAut.conjNormal (m : D)).toMonoidHom
    let b : commutator D →* HexEvenAutomorphisms :=
      (MulAut.conjNormal (v m)).toMonoidHom.comp e.toMonoidHom
    have hab : a = b := by
      apply monoidHom_eq_of_isPerfect_of_comp_eq hexEvenCoordinate
        Representation.Hexacode.even_kernel_eq_center.le a b
      apply MonoidHom.ext
      intro x
      apply Subtype.ext
      change hexCoordinateSixHom
          (e (MulAut.conjNormal (m : D) x) : HexAutomorphisms) =
        hexCoordinateSixHom
          (MulAut.conjNormal (v m) (e x) : HexAutomorphisms)
      rw [he_point]
      change projection c ((m : D) * (x : D) * (m : D)⁻¹) =
        hexCoordinateSixHom (v m * (e x : HexAutomorphisms) * (v m)⁻¹)
      simp only [map_mul, map_inv, hv_point m, he_point x]
    exact congrArg Subtype.val (DFunLike.congr_fun hab n)
  obtain ⟨E, hE, hM⟩ := NormalSupplementGluing.exists_equiv
    (commutator D) M hexSign.ker e v hgen hgen' hinter hagree hconj
  refine ⟨E, ?_⟩
  let f := hexCoordinateSixHom.comp E.toMonoidHom
  have hall : commutator D ⊔ M ≤ f.eqLocus (projection c) := by
    apply sup_le
    · intro n hn
      change hexCoordinateSixHom (E n) = projection c n
      rw [hE ⟨n, hn⟩]
      exact he_point ⟨n, hn⟩
    · intro m hm
      change hexCoordinateSixHom (E m) = projection c m
      rw [hM ⟨m, hm⟩]
      exact hv_point ⟨m, hm⟩
  apply MonoidHom.ext
  intro g
  apply hall
  rw [hgen]
  exact mem_top g

/-- The comparison needed by the surviving terminal quotient alternative. -/
theorem nonempty_hexacode_equiv [Finite D] (c : TripleSymmetric D 6) :
    Nonempty (D ≃* HexAutomorphisms) := by
  obtain ⟨e, _⟩ := exists_hexacode_equiv c
  exact ⟨e⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.TripleSymmetric
