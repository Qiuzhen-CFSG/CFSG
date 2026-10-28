module
public import Stellmacher.SL2DerivedCard
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.Commutator.Finite

/-!
# An elementary three-subgroup supplement in a normal SL₂(2) product

Let `E` be a normal internal product of SL₂(2) factors in a finite group,
and suppose `E` together with a Sylow two-subgroup generates the group.
Then the ambient image of the derived subgroup of `E` is a normal elementary
abelian three-subgroup that also supplements that Sylow subgroup.

The product-coordinate homomorphism identifies the derived image. Each
factor's derived subgroup has order three, so its coordinates commute and
have cube one. Each factor modulo its derived subgroup has order two, which
puts the square of every element of `E` into the derived image. In the
ambient quotient by this normal image, `E` is therefore a normal two-group
and lies in the image of the chosen Sylow subgroup. Lifting that containment
proves the required generation statement.

This is the finite-group supplement calculation for Stellmacher (8.4)'s
faithful SL₂-product quotient, using the factors of (1.7), in
`refs/latex/stellmacher-n-group.tex`. It requires no action hypotheses.
-/

namespace Stellmacher.SectionOne

private theorem derived_data
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct E F)
    (hSL : ∀ D ∈ F, IsSL2Two D) :
    IsElementaryAbelian 3 ((commutator E).map E.subtype) ∧
      ∀ e : E, (e : G) ^ 2 ∈ (commutator E).map E.subtype := by
  classical
  let I := {D : Subgroup G // D ∈ F}
  let P := ∀ i : I, (i : Subgroup G)
  have hc : Pairwise (fun i j : I => ∀ x y : G,
      x ∈ (i : Subgroup G) → y ∈ (j : Subgroup G) → Commute x y) := by
    intro i j hij x y hx hy
    exact hprod.2.2.2 i i.property j j.property
      (fun heq => hij (Subtype.ext heq)) x hx y hy
  let f : P →* G := Subgroup.noncommPiCoprod hc
  have hf : f.range = E := Subgroup.noncommPiCoprod_range.trans hprod.1.symm
  have hm : (commutator P).map f = (commutator E).map E.subtype := by
    rw [map_commutator_eq, hf, Subgroup.map_subtype_commutator]
  have hcard (i : I) : Nat.card (commutator (i : Subgroup G)) = 3 :=
    isSL2Two_commutator_card (hSL i i.property)
  have heval (p : commutator P) (i : I) :
      (p : P) i ∈ commutator (i : Subgroup G) := by
    have h := Subgroup.mem_map_of_mem
      (Pi.evalMonoidHom (fun i : I => (i : Subgroup G)) i) p.property
    rw [map_commutator_eq] at h
    exact Subgroup.commutator_mono le_top le_top h
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPe : IsElementaryAbelian 3 (commutator P) := by
    refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · intro x y
      apply Subtype.ext
      funext i
      let _ : IsCyclic (commutator (i : Subgroup G)) := isCyclic_of_prime_card (hcard i)
      exact congrArg Subtype.val ((IsMulCommutative.is_comm
        (M := commutator (i : Subgroup G))).comm
          ⟨(x : P) i, heval x i⟩ ⟨(y : P) i, heval y i⟩)
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      funext i
      have hh := pow_card_eq_one' (x := (⟨(x : P) i, heval x i⟩ :
        commutator (i : Subgroup G)))
      rw [hcard i] at hh
      exact congrArg Subtype.val hh
  constructor
  · let _ := hPe
    have hh := IsElementaryAbelian.map (p := 3) (A := commutator P) f
    rwa [hm] at hh
  · intro e
    obtain ⟨p, hp⟩ := show (e : G) ∈ f.range from hf ▸ e.property
    rw [← hp, ← map_pow, Subgroup.noncommPiCoprod_apply]
    apply Subgroup.noncommProd_mem
    intro i _
    have hQcard : Nat.card ((i : Subgroup G) ⧸ commutator (i : Subgroup G)) = 2 := by
      have hh := (commutator (i : Subgroup G)).index_mul_card
      rw [Subgroup.index_eq_card, hcard i,
        RankOneThreeGroupAssembly.isSL2Two_card (hSL i i.property)] at hh
      omega
    have hh := pow_card_eq_one' (x := QuotientGroup.mk' (commutator (i : Subgroup G)) (p i))
    rw [hQcard, ← map_pow] at hh
    have hsquare : (p i) ^ 2 ∈ commutator (i : Subgroup G) :=
      (QuotientGroup.eq_one_iff _).mp hh
    have hiE : (i : Subgroup G) ≤ E := by
      rw [hprod.1]
      exact le_iSup (fun j : I => (j : Subgroup G)) i
    have hle : (commutator (i : Subgroup G)).map (i : Subgroup G).subtype ≤
        (commutator E).map E.subtype := by
      rw [Subgroup.map_subtype_commutator, Subgroup.map_subtype_commutator]
      exact Subgroup.commutator_mono hiE hiE
    exact hle (Subgroup.mem_map_of_mem (i : Subgroup G).subtype hsquare)

/-- A normal SL₂(2) product has an elementary-three normal Sylow supplement. -/
public theorem sl2_product_elementary_three_supplement
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (E : Subgroup G) (hEnormal : E.Normal)
    (F : Finset (Subgroup G)) (hprod : IsInternalDirectProduct E F)
    (hSL : ∀ D ∈ F, IsSL2Two D) (hgen : E ⊔ (S : Subgroup G) = ⊤) :
    ∃ R : Subgroup G, R.Normal ∧ IsElementaryAbelian 3 R ∧
      R ⊔ (S : Subgroup G) = ⊤ := by
  let _ := hEnormal
  let R := (commutator E).map E.subtype
  have hRN : R.Normal := by
    dsimp only [R]
    rw [Subgroup.map_subtype_commutator]
    infer_instance
  let _ := hRN
  obtain ⟨hRe, hsquare⟩ := derived_data E F hprod hSL
  refine ⟨R, hRN, hRe, ?_⟩
  let q : G →* G ⧸ R := QuotientGroup.mk' R
  have hE2 : IsPGroup 2 (E.map q) := by
    rintro ⟨x, y, hy, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (q y) ^ (2 ^ 1) = 1
    rw [pow_one, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hsquare ⟨y, hy⟩)
  let _ : (E.map q).Normal := Subgroup.Normal.map hEnormal q (QuotientGroup.mk'_surjective R)
  have hES : E.map q ≤ (S.mapSurjective (QuotientGroup.mk'_surjective R) :
      Subgroup (G ⧸ R)) := hE2.le_sylow_of_normal _
  have hle : E ≤ R ⊔ (S : Subgroup G) := by
    intro e he
    have hh := hES (Subgroup.mem_map_of_mem q he)
    change q e ∈ (S : Subgroup G).map q at hh
    obtain ⟨s, hs, hse⟩ := hh
    have hker : e * s⁻¹ ∈ R := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (e * s⁻¹) = 1
      rw [map_mul, map_inv, hse, mul_inv_cancel]
    have hh := (R ⊔ (S : Subgroup G)).mul_mem
      ((show R ≤ R ⊔ (S : Subgroup G) from le_sup_left) hker)
      ((show (S : Subgroup G) ≤ R ⊔ (S : Subgroup G) from le_sup_right) hs)
    simpa using hh
  exact top_unique (hgen ▸ sup_le hle le_sup_right)

end Stellmacher.SectionOne
