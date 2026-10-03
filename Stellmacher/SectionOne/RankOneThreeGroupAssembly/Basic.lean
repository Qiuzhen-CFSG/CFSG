module

public import Stellmacher.SectionOne.LemmaOneFour
public import Stellmacher.SectionOne.LemmaOneFive
public import Stellmacher.SectionOne.RankOneLocalFullCoordinate
public import Stellmacher.SectionOne.CThreeCtwoSLTwo
public import FeitThompson.PCore.PPrimeCoreFactorization
public import FeitThompson.Fitting.Centralizer
public import Theory.GroupAction.Quotient
public import Theory.GroupAction.Invariant
public import Theory.Representation.CommutingCThreeCTwo
public import Mathlib.GroupTheory.GroupAction.OfQuotient

/-!
# Restriction, invariance and injective quotient maps

Quotient cardinal preservation gives injectivity; commutator closure transports actions through quotient and subgroup maps.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
The conjugation transport of action commutators is also exported for the
conjugacy-invariant factor family assembled in (1.7).
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

public theorem isElementaryAbelian_subgroup
    {p : ℕ} {G : Type u} [Group G] [IsElementaryAbelian p G]
    (A : Subgroup G) : IsElementaryAbelian p A := by
  refine {
    toIsMulCommutative := {
      is_comm := ⟨fun a b =>
        Subtype.ext (IsMulCommutative.is_comm.comm (a : G) (b : G))⟩ }
    exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro a
  apply Subtype.ext
  simpa using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p p G) (a : G)

public theorem isInvariant_restrict_actor
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (A : Subgroup G) (X : Subgroup V) [IsInvariant G V X] :
    IsInvariant A V X := by
  refine ⟨?_⟩
  intro a v
  simpa only [Subgroup.smul_def] using
    (IsInvariant.invariant (A := G) (G := V) (H := X) (a : G) v)

public theorem commutatorAction_isInvariant_of_normal_actor
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (A : Subgroup G) [A.Normal] :
    IsInvariant G V (commutatorAction A V) := by
  have hforward : ∀ g : G, ∀ v : V,
      v ∈ commutatorAction A V → g • v ∈ commutatorAction A V := by
    intro g v hv
    rw [commutatorAction_eq_closure] at hv ⊢
    refine Subgroup.closure_induction
      (p := fun x _ => g • x ∈ Subgroup.closure
        {x : V | ∃ a : A, ∃ w : V, x = w⁻¹ * a • w})
      (x := v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨a, w, rfl⟩
      refine Subgroup.subset_closure
        ⟨⟨g * (a : G) * g⁻¹,
          (inferInstance : A.Normal).conj_mem (a : G) a.property g⟩,
          g • w, ?_⟩
      change g • (w⁻¹ * ((a : G) • w)) = _
      have hconj : g • ((a : G) • w) =
          (g * (a : G) * g⁻¹) • (g • w) := by
        simp [smul_smul, mul_assoc]
      rw [smul_mul', smul_inv', hconj]
      rfl
    · simp
    · intro x y _ _ hx hy
      simpa [smul_mul'] using Subgroup.mul_mem _ hx hy
    · intro x _ hx
      simpa [smul_inv'] using Subgroup.inv_mem _ hx
  refine ⟨?_⟩
  intro g v
  constructor
  · exact hforward g v
  · intro hgv
    have := hforward g⁻¹ (g • v) hgv
    simpa [inv_smul_smul] using this

public theorem subgroup_card_two_eq_zpowers_of_mem_ne_one
    {G : Type u} [Group G] [Finite G]
    (T : Subgroup G) (hTcard : Nat.card T = 2)
    {t : G} (htT : t ∈ T) (htne : t ≠ 1) :
    T = Subgroup.zpowers t := by
  apply le_antisymm
  · have hcardZ : Nat.card (Subgroup.zpowers t) = 2 := by
      have ht2 : t ^ 2 = 1 := by
        obtain ⟨s, hs_ne, hs_unique⟩ := (Nat.card_eq_two_iff' (1 : T)).mp hTcard
        have ht_eq : (⟨t, htT⟩ : T) = s := hs_unique ⟨t, htT⟩ (by
          intro h
          exact htne (congrArg Subtype.val h))
        have ht_sq_mem : t ^ 2 ∈ T := T.pow_mem htT 2
        by_cases ht_sq : t ^ 2 = 1
        · exact ht_sq
        · have hsq_eq : (⟨t ^ 2, ht_sq_mem⟩ : T) = s :=
            hs_unique ⟨t ^ 2, ht_sq_mem⟩ (by
              intro h
              exact ht_sq (congrArg Subtype.val h))
          have h := congrArg Subtype.val (hsq_eq.trans ht_eq.symm)
          have hmul : t * t = t * 1 := by simpa [pow_two] using h
          exact (htne (mul_left_cancel hmul)).elim
      rw [Nat.card_zpowers, orderOf_eq_prime ht2 htne]
    exact (Subgroup.eq_of_le_of_card_ge
      ((Subgroup.zpowers_le).mpr htT)
      (by rw [hTcard, hcardZ])).symm.le
  · exact (Subgroup.zpowers_le).mpr htT

/-- The counting step behind the source's conclusion
`|[W,A]| = 3 or 9`.  If multiplication of two involutions acts on the set of
order-three direct factors by symmetric difference, the second involution
has exactly one new support factor, and it was chosen no larger than its
product with the first involution, then minimality bounds the first support
by two factors. -/
public theorem card_le_two_of_minimal_symmDiff
    {ι : Type*} [DecidableEq ι] (A X : Finset ι)
    (hnew : (X \ A).card = 1)
    (hglobal : A.card ≤ X.card)
    (hlocal : X.card ≤ (A ∆ X).card) :
    A.card ≤ 2 := by
  have hsymm : (A ∆ X).card = (A \ X).card + (X \ A).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro a ha hcontra
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hcontra).1
  have hX : X.card = (X \ A).card + (A ∩ X).card := by
    rw [← Finset.card_sdiff_add_card_inter X A, Finset.inter_comm]
  have hA : A.card = (A \ X).card + (A ∩ X).card := by
    exact (Finset.card_sdiff_add_card_inter A X).symm
  rw [hnew] at hsymm hX
  omega

@[expose] public def restrictedMap
    {G Q : Type*} [Group G] [Group Q]
    (K : Subgroup G) (f : G →* Q) : K →* K.map f :=
  (f.domRestrict K).codRestrict (K.map f) fun x => ⟨x, x.property, rfl⟩

public theorem restrictedMap_injective_of_natCard_map_eq
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (K : Subgroup G) (f : G →* Q)
    (hcard : Nat.card (K.map f) = Nat.card K) :
    Function.Injective (restrictedMap K f) := by
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (K.map f) := Fintype.ofFinite (K.map f)
  have hsurj : Function.Surjective (restrictedMap K f) := by
    rintro ⟨y, x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    exact hxy
  exact (Fintype.bijective_iff_surjective_and_card
    (restrictedMap K f)).2 ⟨hsurj, by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hcard.symm⟩ |>.1

public theorem inf_ker_eq_bot_of_natCard_map_eq
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (K : Subgroup G) (f : G →* Q)
    (hcard : Nat.card (K.map f) = Nat.card K) :
    K ⊓ f.ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxone : restrictedMap K f ⟨x, hx.1⟩ =
      restrictedMap K f 1 := by
    apply Subtype.ext
    change f x = f 1
    simpa using MonoidHom.mem_ker.mp hx.2
  have := restrictedMap_injective_of_natCard_map_eq K f hcard hxone
  exact congrArg (fun z : K => (z : G)) this

/-- Normality also lifts through a homomorphism whose restriction to a
subgroup is injective.  This is the exact mechanism needed below: a local
derived factor is normal in the quotient, and its cardinal-preserving lift
lies in a normal subgroup on which the quotient map is injective. -/
public theorem normal_of_map_normal_of_le_of_inf_ker_eq_bot
    {G Q : Type*} [Group G] [Group Q]
    (K L : Subgroup G) (f : G →* Q)
    (hKnormal : K.Normal) (hLK : L ≤ K)
    (hmapNormal : (L.map f).Normal)
    (hker : K ⊓ f.ker = ⊥) : L.Normal := by
  constructor
  intro l hl g
  have hconjK : g * l * g⁻¹ ∈ K := hKnormal.conj_mem l (hLK hl) g
  have hmapConj : f (g * l * g⁻¹) ∈ L.map f := by
    simpa using hmapNormal.conj_mem (f l) ⟨l, hl, rfl⟩ (f g)
  rcases hmapConj with ⟨l', hl', hfl'⟩
  have hl'K : l' ∈ K := hLK hl'
  have hdiff : l'⁻¹ * (g * l * g⁻¹) ∈ K ⊓ f.ker := by
    refine ⟨K.mul_mem (K.inv_mem hl'K) hconjK, MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_inv, ← hfl']
    simp
  have hdiff_one : l'⁻¹ * (g * l * g⁻¹) = 1 := by
    rw [hker] at hdiff
    exact hdiff
  have hconj_eq : g * l * g⁻¹ = l' := by
    calc
      g * l * g⁻¹ = l' * (l'⁻¹ * (g * l * g⁻¹)) := by simp
      _ = l' := by rw [hdiff_one]; simp
  rw [hconj_eq]
  exact hl'

/-- Two subgroups of a subgroup on which a homomorphism is injective are
equal as soon as their images are equal.  The kernel condition is phrased in
the ambient group so it can be discharged by
`inf_ker_eq_bot_of_natCard_map_eq`. -/
public theorem eq_of_le_of_map_eq_of_inf_ker_eq_bot
    {G Q : Type*} [Group G] [Group Q]
    (K L : Subgroup G) (f : G →* Q)
    (hLK : L ≤ K) (hmap : L.map f = K.map f)
    (hker : K ⊓ f.ker = ⊥) : L = K := by
  apply le_antisymm hLK
  intro k hkK
  have hfk : f k ∈ L.map f := by
    rw [hmap]
    exact ⟨k, hkK, rfl⟩
  obtain ⟨l, hlL, hfl⟩ := hfk
  have hlK : l ∈ K := hLK hlL
  have hdiff : l⁻¹ * k ∈ K ⊓ f.ker := by
    refine ⟨K.mul_mem (K.inv_mem hlK) hkK, MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_inv, hfl]
    simp
  have hdiff_one : l⁻¹ * k = 1 := by
    rw [hker] at hdiff
    exact hdiff
  have hk_eq_l : k = l := by
    calc
      k = l * (l⁻¹ * k) := by simp
      _ = l := by rw [hdiff_one]; simp
  rw [hk_eq_l]
  exact hlL

/-- Two subgroups of a common subgroup on which a homomorphism is injective
are equal when their images are equal. -/
public theorem eq_of_le_of_le_of_map_eq_of_inf_ker_eq_bot
    {G Q : Type*} [Group G] [Group Q]
    (K L M : Subgroup G) (f : G →* Q)
    (hLK : L ≤ K) (hMK : M ≤ K) (hmap : L.map f = M.map f)
    (hker : K ⊓ f.ker = ⊥) : L = M := by
  have aux (X Y : Subgroup G) (hXK : X ≤ K) (hYK : Y ≤ K)
      (hXY : X.map f = Y.map f) : X ≤ Y := by
    intro x hxX
    have hfx : f x ∈ Y.map f := hXY ▸ ⟨x, hxX, rfl⟩
    obtain ⟨y, hyY, hfy⟩ := hfx
    have hdiff : y⁻¹ * x ∈ K ⊓ f.ker := by
      refine ⟨K.mul_mem (K.inv_mem (hYK hyY)) (hXK hxX),
        MonoidHom.mem_ker.mpr ?_⟩
      rw [map_mul, map_inv, hfy]
      simp
    have hdiff_one : y⁻¹ * x = 1 := by
      rw [hker] at hdiff
      exact hdiff
    have hxy : x = y := by
      calc
        x = y * (y⁻¹ * x) := by simp
        _ = y := by rw [hdiff_one]; simp
    rw [hxy]
    exact hyY
  exact le_antisymm (aux L M hLK hMK hmap)
    (aux M L hMK hLK hmap.symm)

public theorem fixedPoints_isInvariant_of_normal
    {H V : Type*} [Group H] [Group V] [MulDistribMulAction H V]
    (A : Subgroup H) [A.Normal] :
    IsInvariant H V (FixedPoints.subgroup A V) := by
  refine ⟨?_⟩
  intro h v
  constructor
  · intro hv
    rw [FixedPoints.mem_subgroup]
    intro a
    have hconj : h⁻¹ * (a : H) * h ∈ A := by
      simpa using (inferInstance : A.Normal).conj_mem (a : H) a.property h⁻¹
    have hfix := (FixedPoints.mem_subgroup (M := A) (a := v)).1 hv
      ⟨h⁻¹ * (a : H) * h, hconj⟩
    have hfix' : (h⁻¹ * (a : H) * h) • v = v := hfix
    calc
      (a : H) • (h • v) = ((a : H) * h) • v := by rw [mul_smul]
      _ = h • ((h⁻¹ * (a : H) * h) • v) := by
        simp only [← mul_smul]
        congr 1
        group
      _ = h • v := by rw [hfix']
  · intro hv
    have hinv : h⁻¹ • (h • v) ∈ FixedPoints.subgroup A V := by
      rw [FixedPoints.mem_subgroup]
      intro a
      have hconj : h * (a : H) * h⁻¹ ∈ A :=
        (inferInstance : A.Normal).conj_mem (a : H) a.property h
      have hfix := (FixedPoints.mem_subgroup (M := A) (a := h • v)).1 hv
        ⟨h * (a : H) * h⁻¹, hconj⟩
      have hfix' : (h * (a : H) * h⁻¹) • (h • v) = h • v := hfix
      calc
        (a : H) • (h⁻¹ • (h • v)) =
            h⁻¹ • ((h * (a : H) * h⁻¹) • (h • v)) := by
          simp only [← mul_smul]
          congr 1
          group
        _ = h⁻¹ • (h • v) := by rw [hfix']
    simpa [smul_smul] using hinv

/-- Passing from a subgroup to its image in a quotient does not change its
commutator action on the fixed points of the quotient kernel. -/
private theorem commutatorAction_map_quotient_fixedPoints_eq
    {H V : Type*} [Group H] [Group V] [MulDistribMulAction H V]
    (A : Subgroup H) [A.Normal]
    [IsInvariant H V (FixedPoints.subgroup A V)]
    (L : Subgroup H) :
    commutatorAction (L.map (QuotientGroup.mk' A))
        (FixedPoints.subgroup A V) =
      commutatorAction L (FixedPoints.subgroup A V) := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨d, w, rfl⟩
    rcases d.property with ⟨l, hl, hld⟩
    refine ⟨⟨l, hl⟩, w, ?_⟩
    apply congrArg (fun z : FixedPoints.subgroup A V => w⁻¹ * z)
    rw [Subgroup.smul_def, Subgroup.smul_def, ← hld]
    exact MulAction.coe_quotient_smul_fixedPoints l w
  · rintro ⟨l, w, rfl⟩
    let d : L.map (QuotientGroup.mk' A) :=
      ⟨QuotientGroup.mk' A l, ⟨l, l.property, rfl⟩⟩
    refine ⟨d, w, ?_⟩
    apply congrArg (fun z : FixedPoints.subgroup A V => w⁻¹ * z)
    rw [Subgroup.smul_def, Subgroup.smul_def]
    exact (MulAction.coe_quotient_smul_fixedPoints
      (G := H) (A := V) (H := A) l w).symm

public theorem commutatorAction_lift_card_eq
    {H V : Type*} [Group H] [Group V] [Finite V]
    [MulDistribMulAction H V]
    (A : Subgroup H) [A.Normal]
    [IsInvariant H V (FixedPoints.subgroup A V)]
    (L : Subgroup H) (D : Subgroup (H ⧸ A))
    (hmap : L.map (QuotientGroup.mk' A) = D)
    (hcard : Nat.card
      (commutatorAction D (FixedPoints.subgroup A V)) = 4) :
    Nat.card (commutatorAction L (FixedPoints.subgroup A V)) = 4 := by
  rw [← commutatorAction_map_quotient_fixedPoints_eq A L, hmap]
  exact hcard

public theorem commutatorAction_map_subtype_mono
    {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]
    (H K : Subgroup V) [IsInvariant A V H] [IsInvariant A V K]
    (hHK : H ≤ K) :
    (commutatorAction A H).map H.subtype ≤
      (commutatorAction A K).map K.subtype := by
  rw [commutatorAction_eq_closure, MonoidHom.map_closure,
    commutatorAction_eq_closure, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro x ⟨z, ⟨a, h, rfl⟩, rfl⟩
  let k : K := ⟨h, hHK h.property⟩
  refine ⟨k⁻¹ * a • k, ⟨a, k, rfl⟩, ?_⟩
  rfl

public theorem isInvariant_of_subgroup
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (H F : Subgroup G) (U : Subgroup V)
    [IsInvariant H V U] (hFH : F ≤ H) : IsInvariant F V U := by
  refine ⟨?_⟩
  intro f v
  exact IsInvariant.invariant (A := H) (G := V) (H := U)
    ⟨f, hFH f.property⟩ v

/-- Conjugating an acting subgroup transports its action commutator by the
same ambient automorphism of the module. -/
public theorem commutatorAction_conjBy
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (F : Subgroup G) (g : G) :
    (commutatorAction F V).map
        (MulDistribMulAction.toMulAut G V g).toMonoidHom =
      commutatorAction (F.conjBy g) V := by
  rw [commutatorAction_eq_closure, MonoidHom.map_closure,
    commutatorAction_eq_closure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨y, ⟨f, v, rfl⟩, rfl⟩
    let fg : F.conjBy g :=
      ⟨g * (f : G) * g⁻¹, ⟨(f : G), f.property, rfl⟩⟩
    refine ⟨fg, g • v, ?_⟩
    change g • (v⁻¹ * (f : G) • v) =
      (g • v)⁻¹ * (g * (f : G) * g⁻¹) • (g • v)
    simp only [smul_mul', smul_inv', smul_smul]
    congr 1
    group
  · rintro ⟨fg, v, rfl⟩
    rcases fg.property with ⟨f, hf, hfg⟩
    let fF : F := ⟨f, hf⟩
    refine ⟨(g⁻¹ • v)⁻¹ * (fF : G) • (g⁻¹ • v), ⟨fF, g⁻¹ • v, rfl⟩, ?_⟩
    change g • ((g⁻¹ • v)⁻¹ * f • (g⁻¹ • v)) =
      v⁻¹ * (fg : G) • v
    rw [← hfg]
    simp [smul_mul', smul_inv', smul_smul, MulAut.conj_apply, mul_assoc]

/-- Membership in `oneOmega` is invariant under ambient conjugacy. -/
public theorem oneOmega_conjBy
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hF : oneOmega (G := G) (V := V) F) (g : G) :
    oneOmega (G := G) (V := V) (F.conjBy g) := by
  let _ : (oddCore G).Normal := pPrimeCore_normal
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨f, hf, rfl⟩
    exact (inferInstance : (oddCore G).Normal).conj_mem f (hF.1 hf) g
  · change Nat.card (F.map (MulAut.conj g).toMonoidHom) = 3
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hF.2.1
  · rw [← commutatorAction_conjBy F g]
    exact (Subgroup.card_map_of_injective
      (K := commutatorAction F V)
      (f := (MulDistribMulAction.toMulAut G V g).toMonoidHom)
      (MulDistribMulAction.toMulAut G V g).injective).trans hF.2.2

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
