module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Kernel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.FieldPowers
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups
public import Theory.SpecificGroups.ReeF4.CartanFieldAction
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation

/-!
# Ree Cartan actions in the invariant embedding argument

Under inner–field coverage, the actual Ree outer group has odd order.
Consequently every two-subgroup of an overgroup with generalized Fitting
subgroup D lies in D. If B normalizes S ∩ D, the commutator of an element
of N_S(B) with B lies in the disjoint two- and p-subgroups S and B, so it
is trivial. This gives the required power action on the actual B/Φ(B).

`Source.RawCartan` retains the full A.3.15(5) configuration in Aut(D), with
an actual D ≃* ReeF4.Model m, cyclic F of order f dividing n = 2m + 1,
an F-invariant Cartan H of N_I(S ∩ D), B ≤ FH, FBD = HBD, and the actual
inner-diagonal part I. The source convention allows each field automorphism
its own conjugating automorphism. Cyclicity supplies common coordinates for F;
coverage reduces their conjugating automorphism to an inner one. The proved
matrix-trace separation theorem then eliminates the field factor of B ≤ D.
The remaining Cartan action normalizes S ∩ D in the original ambient group.

`Source.frattini_power_of_raw_cartan` completes this action argument with only
universal inner–field coverage left explicit, as permitted by its assembly
owner. The model construction is supplied by `canonicalLocalBlockInput`, and
`modelEquiv` identifies any local input with the actual carrier. No Cartan
alignment, field separation, inner-diagonal realization, or power action is
assumed. The earlier low-level adapters retain their public signatures.
The source configuration requires m ≥ 1; the low-level algebra at m = 0
concerns the full Ree fixed group and does not identify the Tits group.

Source: Aschbacher–Smith, Lemma A.3.15(5), printed pp.50–51, and the proof of
Proposition 1.3.4, printed p.511 (`refs/quasithin.pdf`, combined 1 March 2004
manuscript). The Cartan and field conventions are those of A.2.5 and GLS3 §2.5.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Ree
/-- Odd Ree outer order forces every two-subgroup into a self-centralizing normal subgroup. -/
theorem two_subgroup_le {J : Type*} [Group J] [Finite J] (D S : Subgroup J) [D.Normal]
    (hCD : centralizer (D : Set J) ≤ D) (hS : IsPGroup 2 S)
    {m : ℕ} (d : ReeF4.LocalBlockInput m) (e : D ≃* d.fixedGroup)
    (hcover : ∀ a : MulAut d.fixedGroup, ∃ (g : d.fixedGroup) (k : ℤ),
      a = MulAut.conj g * d.fieldAutomorphism ^ k) : S ≤ D := by
  have ho : Odd (Nat.card (MulAut.Outer D)) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact Odd.of_dvd_nat ⟨m, rfl⟩ (d.outer_card_dvd_of_inner_field hcover)
  let f : J →* MulAut.Outer D :=
    (QuotientGroup.mk' (MulAut.innerSubgroup D)).comp MulAut.conjNormal
  intro s hs
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hpow : f s ^ (2 ^ k) = 1 := by
    rw [← map_pow, show s ^ (2 ^ k) = 1 from congrArg Subtype.val hk, map_one]
  have hord : orderOf (f s) = 1 := Nat.eq_one_of_dvd_coprimes
    (ho.coprime_two_left.pow_left k) (orderOf_dvd_of_pow_eq_one hpow)
    (orderOf_dvd_natCard _)
  have hi : MulAut.conjNormal s ∈ MulAut.innerSubgroup D :=
    (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hord)
  have hc : s ∈ D ⊔ centralizer (D : Set J) := by
    rw [← MulAut.conjNormal_comap_innerSubgroup D]
    exact hi
  exact (sup_le le_rfl hCD) hc

open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions
variable {J : Type*} [Group J] [Finite J]

/-- A nonabelian simple generalized Fitting subgroup has trivial ambient centralizer. -/
private theorem centralizer_fitting_simple (D : Subgroup J) [IsSimpleGroup D]
    (hD : generalizedFitting J = D) (hnab : ¬ IsMulCommutative D) :
    centralizer (D : Set J) = ⊥ := by
  have hCD : centralizer (D : Set J) ≤ D := by
    rw [← hD]
    exact CFSG.Quasithin.ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hz : center D = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center D) inferInstance with h | h
    · exact h
    · exact (hnab (center_eq_top_iff.mp h)).elim
  apply bot_unique
  intro x hx
  have hxD := hCD hx
  have hxZ : (⟨x, hxD⟩ : D) ∈ center D := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
  have he : (⟨x, hxD⟩ : D) = 1 := mem_bot.mp (hz ▸ hxZ)
  exact congrArg Subtype.val he

/-- Once B normalizes the inner Sylow subgroup, the entire Sylow normalizer action is trivial. -/
theorem normalizer_kernel (D B : Subgroup J) [D.Normal]
    (hCD : centralizer (D : Set J) ≤ D) (S : Sylow 2 J)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hB : IsPGroup p B)
    (hn : B ≤ normalizer ((S : Subgroup J) ⊓ D : Subgroup J))
    {m : ℕ} (d : ReeF4.LocalBlockInput m) (e : D ≃* d.fixedGroup)
    (hcover : ∀ a : MulAut d.fixedGroup, ∃ (g : d.fixedGroup) (k : ℤ),
      a = MulAut.conj g * d.fieldAutomorphism ^ k) :
    (S : Subgroup J) ⊓ normalizer B ≤ centralizer (B : Set J) := by
  have hSD := two_subgroup_le D S hCD S.isPGroup' d e hcover
  have hn' : B ≤ normalizer (S : Subgroup J) := by
    simpa only [inf_eq_left.mpr hSD] using hn
  have hd := IsPGroup.disjoint_of_ne 2 p (by omega) S B S.isPGroup' hB
  intro s hs
  exact unipotent_centralizes S B hd hn' hs.1 hs.2

/-- The actual Frattini action is by powers once the raw Cartan normalization is established. -/
theorem frattini_power_of_normalizes (D B : Subgroup J) [D.Normal]
    (hD : generalizedFitting J = D) (S : Sylow 2 J)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hB : IsPGroup p B)
    (hn : B ≤ normalizer ((S : Subgroup J) ⊓ D : Subgroup J))
    {m : ℕ} (d : ReeF4.LocalBlockInput m) (e : D ≃* ReeF4.Model m)
    (hcover : ∀ a : MulAut d.fixedGroup, ∃ (g : d.fixedGroup) (k : ℤ),
      a = MulAut.conj g * d.fieldAutomorphism ^ k) :
    ∀ (s : ((S : Subgroup J) ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  have hCD : centralizer (D : Set J) ≤ D := by
    rw [← hD]
    exact CFSG.Quasithin.ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  apply frattini_action_pow
  intro s
  refine ⟨1, fun b => ?_⟩
  have hs := normalizer_kernel D B hCD S hp hB hn d
    (e.trans d.modelEquiv.symm) hcover s.property
  rw [← mem_centralizer_iff.mp hs b b.property, mul_inv_cancel_right, pow_one]

/-- The actual ambient conjugation action, transported to the concrete Ree fixed group. -/
noncomputable def modelAction (D : Subgroup J) [D.Normal]
    {m : ℕ} (d : ReeF4.LocalBlockInput m) (e : D ≃* ReeF4.Model m) :
    J →* MulAut d.fixedGroup :=
  (MulAut.congr (e.trans d.modelEquiv.symm)).toMonoidHom.comp MulAut.conjNormal

omit [Finite J] in
/-- On D the transported action is conjugation by the corresponding actual matrix. -/
theorem modelAction_on_subgroup (D : Subgroup J) [D.Normal]
    {m : ℕ} (d : ReeF4.LocalBlockInput m) (e : D ≃* ReeF4.Model m) (x : D) :
    modelAction D d e x = MulAut.conj (d.modelEquiv.symm (e x)) := by
  change MulAut.congr (e.trans d.modelEquiv.symm) (MulAut.conjNormal x) = _
  rw [MulAut.conjNormal_val, MulAut.congr_conj]
  rfl

/-- The generalized-Fitting hypothesis makes the transported conjugation faithful. -/
theorem modelAction_injective (D : Subgroup J) [D.Normal] [IsSimpleGroup D]
    (hD : generalizedFitting J = D) (hnab : ¬ IsMulCommutative D)
    {m : ℕ} (d : ReeF4.LocalBlockInput m) (e : D ≃* ReeF4.Model m) :
    Function.Injective (modelAction D d e) :=
  (MulAut.congr (e.trans d.modelEquiv.symm)).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot D
      (centralizer_fitting_simple D hD hnab))

omit [Finite J] in
private theorem raw_alignment {A : Type*} [Group A] (f : J →* A)
    (hf : Function.Injective f) (B U : Subgroup J) (F H I : Subgroup A)
    (hBI : B.map f ≤ I) (hHI : H ≤ I) (hFI : Disjoint F I)
    (hHN : H ≤ normalizer (U.map f : Set A))
    (hprod : ∀ b ∈ B, ∃ a ∈ F, ∃ h ∈ H, f b = a * h) :
    B ≤ normalizer (U : Set J) := by
  have hBH : B.map f ≤ H := by
    apply le_cartan_of_field_inner_disjoint _ F H I hBI hHI hFI
    rintro x ⟨b, hb, rfl⟩
    exact hprod b hb
  have he : (normalizer (U.map f : Set A)).comap f = normalizer (U : Set J) := by
    rw [comap_normalizer_eq_of_le_range (map_le_range f U),
      comap_map_eq_self_of_injective hf]
  rw [← he]
  exact map_le_iff_le_comap.mp (hBH.trans hHN)

private theorem disjoint_conjugate_field {A : Type*} [Group A]
    (φ : A) (I : Subgroup A) (hφ : Disjoint (zpowers φ) I) (g : A) (hg : g ∈ I) :
    Disjoint ((zpowers φ).map (MulAut.conj g).toMonoidHom) I := by
  apply disjoint_def.mpr
  rintro x ⟨b, hb, rfl⟩ hx
  have hbI : b ∈ I := by
    have hh := I.mul_mem (I.inv_mem hg) (I.mul_mem hx hg)
    simpa using hh
  have hb1 : b = 1 := hφ.le_bot ⟨hb, hbI⟩
  simp [hb1]


/-- A low-level adapter for an inner-conjugate field subgroup. The explicit
separation argument is supplied by `ReeF4.Cartan.field_disjoint_innerDiagonal`. -/
theorem frattini_power_of_inner_conjugate_field (D B : Subgroup J)
    [D.Normal] [IsSimpleGroup D]
    (hD : generalizedFitting J = D) (hnab : ¬ IsMulCommutative D)
    (S : Sylow 2 J) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hB : IsPGroup p B) (hBD : B ≤ D)
    {m : ℕ} (d : ReeF4.LocalBlockInput m) (e : D ≃* ReeF4.Model m)
    (F H : Subgroup (MulAut d.fixedGroup)) (g : d.fixedGroup)
    (hF : F ≤ (zpowers d.fieldAutomorphism).map
      (MulAut.conj (MulAut.conj g)).toMonoidHom)
    (hHI : H ≤ ReeF4.Cartan.innerDiagonal d)
    (hHN : H ≤ normalizer
      (((S : Subgroup J) ⊓ D).map (modelAction D d e) : Set (MulAut d.fixedGroup)))
    (hprod : ∀ b ∈ B, ∃ a ∈ F, ∃ h ∈ H, modelAction D d e b = a * h)
    (hcover : ∀ a : MulAut d.fixedGroup, ∃ (g : d.fixedGroup) (k : ℤ),
      a = MulAut.conj g * d.fieldAutomorphism ^ k)
    (hsep : Disjoint (zpowers d.fieldAutomorphism) (ReeF4.Cartan.innerDiagonal d)) :
    ∀ (s : ((S : Subgroup J) ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  have hFI : Disjoint F (ReeF4.Cartan.innerDiagonal d) := by
    exact (disjoint_conjugate_field d.fieldAutomorphism _ hsep
      (MulAut.conj g) (ReeF4.Cartan.inner_le_innerDiagonal d ⟨g, rfl⟩)).mono_left hF
  have hBI : B.map (modelAction D d e) ≤ ReeF4.Cartan.innerDiagonal d := by
    rintro a ⟨b, hb, rfl⟩
    apply ReeF4.Cartan.inner_le_innerDiagonal
    refine ⟨d.modelEquiv.symm (e ⟨b, hBD hb⟩), ?_⟩
    exact (modelAction_on_subgroup D d e ⟨b, hBD hb⟩).symm
  have hn : B ≤ normalizer ((S : Subgroup J) ⊓ D : Subgroup J) :=
    raw_alignment (modelAction D d e) (modelAction_injective D hD hnab d e)
      B ((S : Subgroup J) ⊓ D) F H (ReeF4.Cartan.innerDiagonal d) hBI hHI hFI hHN hprod
  exact frattini_power_of_normalizes D B hD S hp hB hn d e hcover

private theorem conjugate_field_subgroup {A : Type*} [Group A] (φ i : A) (k : ℤ) :
    (zpowers φ).map (MulAut.conj (i * φ ^ k)).toMonoidHom =
      (zpowers φ).map (MulAut.conj i).toMonoidHom := by
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  congr 1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  calc
    i * φ ^ k * φ * ((φ ^ k)⁻¹ * i⁻¹) =
        i * (φ ^ k * φ) * (φ ^ k)⁻¹ * i⁻¹ := by simp only [mul_assoc]
    _ = i * φ * i⁻¹ := by
      rw [(Commute.zpow_self φ k).eq]
      simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- The raw field subgroup may be conjugated by any automorphism, in accordance
with GLS3's field-automorphism convention. The source Cartan is only required
to lie in the inner-diagonal part of the indicated Sylow normalizer. Canonical
field/inner-diagonal separation is retained as an explicit argument for
compatibility; `Source.frattini_power_of_raw_cartan` discharges it. -/
theorem frattini_power_of_raw_cartan (D B : Subgroup J)
    [D.Normal] [IsSimpleGroup D]
    (hD : generalizedFitting J = D) (hnab : ¬ IsMulCommutative D)
    (S : Sylow 2 J) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hB : IsPGroup p B) (hBD : B ≤ D)
    {m : ℕ} (d : ReeF4.LocalBlockInput m) (e : D ≃* ReeF4.Model m)
    (F H : Subgroup (MulAut d.fixedGroup)) (a : MulAut d.fixedGroup)
    (hF : F ≤ (zpowers d.fieldAutomorphism).map (MulAut.conj a).toMonoidHom)
    (hHI : H ≤ ReeF4.Cartan.innerDiagonal d)
    (hHN : H ≤ normalizer
      (((S : Subgroup J) ⊓ D).map (modelAction D d e) : Set (MulAut d.fixedGroup)))
    (hprod : ∀ b ∈ B, ∃ f ∈ F, ∃ h ∈ H, modelAction D d e b = f * h)
    (hcover : ∀ a : MulAut d.fixedGroup, ∃ (g : d.fixedGroup) (k : ℤ),
      a = MulAut.conj g * d.fieldAutomorphism ^ k)
    (hsep : Disjoint (zpowers d.fieldAutomorphism) (ReeF4.Cartan.innerDiagonal d)) :
    ∀ (s : ((S : Subgroup J) ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  obtain ⟨g, k, rfl⟩ := hcover a
  rw [conjugate_field_subgroup] at hF
  exact frattini_power_of_inner_conjugate_field D B hD hnab S hp hB hBD
    d e F H g hF hHI hHN hprod hcover hsep

namespace Source

open scoped Pointwise

variable (D : Subgroup J) [D.Normal] {m : ℕ}

/-- A field automorphism in the Suzuki–Ree convention of GLS3, 2.5.13:
an arbitrary automorphism-conjugate of a canonical Frobenius power. -/
def IsField (d : ReeF4.LocalBlockInput m) (e : D ≃* ReeF4.Model m)
    (a : MulAut D) : Prop :=
  ∃ (c : MulAut d.fixedGroup) (k : ℤ),
    MulAut.congr (e.trans d.modelEquiv.symm) a =
      c * d.fieldAutomorphism ^ k * c⁻¹

/-- The full field–Cartan configuration of A.3.15(5), on the actual Ree
carrier. The Cartan clauses express an abelian complement to the inner image
of S ∩ D in its normalizer inside I. The auxiliary factors live in Aut(D),
and FBD = HBD is an equality of set products. The parameter restriction
keeps the full binary Ree group and the Tits simple carrier separate. -/
structure RawCartan (d : ReeF4.LocalBlockInput m) (e : D ≃* ReeF4.Model m)
    (S : Sylow 2 J) (B : Subgroup J) (n f : ℕ)
    (F H I : Subgroup (MulAut D)) : Prop where
  parameter_large : 1 ≤ m
  field_degree : n = 2 * m + 1
  field_cyclic : IsCyclic F
  field_order : Nat.card F = f
  field_divides : f ∣ n
  field_type : ∀ a ∈ F, IsField D d e a
  cartan_inside : H ≤ I
  cartan_preserves : ∀ h ∈ H,
    ((S : Subgroup J).subgroupOf D).map h.toMonoidHom = (S : Subgroup J).subgroupOf D
  cartan_abelian : IsMulCommutative H
  cartan_disjoint :
    Disjoint (((S : Subgroup J).subgroupOf D).map (MulAut.conj : D →* MulAut D)) H
  cartan_factorization : ∀ a ∈ I,
    ((S : Subgroup J).subgroupOf D).map a.toMonoidHom = (S : Subgroup J).subgroupOf D ↔
      ∃ u ∈ (S : Subgroup J).subgroupOf D, ∃ h ∈ H, a = MulAut.conj u * h
  invariant : ∀ a ∈ F, H.map (MulAut.conj a).toMonoidHom = H
  contained : ∀ b ∈ B, ∃ a ∈ F, ∃ h ∈ H, MulAut.conjNormal b = a * h
  product : (F : Set (MulAut D)) * (B.map (MulAut.conjNormal (H := D)) : Set (MulAut D)) *
      ((MulAut.conj : D →* MulAut D).range : Set (MulAut D)) =
    (H : Set (MulAut D)) * (B.map (MulAut.conjNormal (H := D)) : Set (MulAut D)) *
      ((MulAut.conj : D →* MulAut D).range : Set (MulAut D))
  inner_diagonal : I =
    (F ⊔ B.map (MulAut.conjNormal (H := D)) ⊔ (MulAut.conj : D →* MulAut D).range) ⊓
      (ReeF4.Cartan.innerDiagonal d).comap
        (MulAut.congr (e.trans d.modelEquiv.symm)).toMonoidHom

omit [Finite J] [D.Normal] in
/-- Cyclicity supplies common field coordinates from the source's
elementwise field-automorphism convention. -/
theorem common_field_coordinates (d : ReeF4.LocalBlockInput m)
    (e : D ≃* ReeF4.Model m) (F : Subgroup (MulAut D))
    (hcyc : IsCyclic F) (hfield : ∀ a ∈ F, IsField D d e a) :
    ∃ c : MulAut d.fixedGroup,
      F.map (MulAut.congr (e.trans d.modelEquiv.symm)).toMonoidHom ≤
        (zpowers d.fieldAutomorphism).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨a, ha⟩ := F.isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  obtain ⟨c, k, he⟩ := hfield a (ha ▸ mem_zpowers a)
  refine ⟨c, ?_⟩
  rw [← ha, MonoidHom.map_zpowers]
  apply zpowers_le.mpr
  change MulAut.congr (e.trans d.modelEquiv.symm) a ∈ _
  rw [he]
  exact mem_map_of_mem (MulAut.conj c).toMonoidHom (zpow_mem_zpowers _ k)

variable {d : ReeF4.LocalBlockInput m} {e : D ≃* ReeF4.Model m}
    {S : Sylow 2 J} {B : Subgroup J} {n f : ℕ} {F H I : Subgroup (MulAut D)}

omit [Finite J] in
/-- Separation eliminates the field factor of each element of B. This
derives containment of its actual action in the given Cartan, without a
canonical Cartan alignment or an inner realization of every diagonal. -/
theorem action_le_cartan (h : RawCartan D d e S B n f F H I) (hBD : B ≤ D)
    (hcover : ∀ a : MulAut d.fixedGroup, ∃ (g : d.fixedGroup) (k : ℤ),
      a = MulAut.conj g * d.fieldAutomorphism ^ k) :
    B.map (modelAction D d e) ≤
      H.map (MulAut.congr (e.trans d.modelEquiv.symm)).toMonoidHom := by
  let c := (MulAut.congr (e.trans d.modelEquiv.symm)).toMonoidHom
  obtain ⟨a, hF⟩ := common_field_coordinates D d e F h.field_cyclic h.field_type
  obtain ⟨g, k, rfl⟩ := hcover a
  rw [conjugate_field_subgroup] at hF
  have hFI : Disjoint (F.map c) (ReeF4.Cartan.innerDiagonal d) :=
    (disjoint_conjugate_field d.fieldAutomorphism _
      (ReeF4.Cartan.field_disjoint_innerDiagonal d) (MulAut.conj g)
      (ReeF4.Cartan.inner_le_innerDiagonal d ⟨g, rfl⟩)).mono_left hF
  have hHI : H.map c ≤ ReeF4.Cartan.innerDiagonal d := by
    rintro _ ⟨a, ha, rfl⟩
    have hi := h.cartan_inside ha
    rw [h.inner_diagonal] at hi
    exact hi.2
  have hBI : B.map (modelAction D d e) ≤ ReeF4.Cartan.innerDiagonal d := by
    rintro a ⟨b, hb, rfl⟩
    apply ReeF4.Cartan.inner_le_innerDiagonal
    refine ⟨d.modelEquiv.symm (e ⟨b, hBD hb⟩), ?_⟩
    exact (modelAction_on_subgroup D d e ⟨b, hBD hb⟩).symm
  apply le_cartan_of_field_inner_disjoint _ (F.map c) (H.map c)
    (ReeF4.Cartan.innerDiagonal d) hBI hHI hFI
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨a, ha, z, hz, he⟩ := h.contained b hb
  refine ⟨c a, mem_map_of_mem c ha, c z, mem_map_of_mem c hz, ?_⟩
  change c (MulAut.conjNormal b) = c a * c z
  rw [he, map_mul]

omit [Finite J] in
/-- The raw Cartan preserves the actual Sylow intersection. Equality of
automorphisms transports this property back to conjugation by B inside J. -/
theorem normalizes_sylow (h : RawCartan D d e S B n f F H I) (hBD : B ≤ D)
    (hcover : ∀ a : MulAut d.fixedGroup, ∃ (g : d.fixedGroup) (k : ℤ),
      a = MulAut.conj g * d.fieldAutomorphism ^ k) :
    B ≤ normalizer ((S : Subgroup J) ⊓ D : Subgroup J) := by
  apply le_normalizer_iff.mpr
  intro b hb x hx
  obtain ⟨a, ha, he⟩ := action_le_cartan D h hBD hcover
    (mem_map_of_mem (modelAction D d e) hb)
  have he' : a = MulAut.conjNormal b :=
    (MulAut.congr (e.trans d.modelEquiv.symm)).injective he
  have hm := mem_map_of_mem a.toMonoidHom
    (show (⟨x, hx.2⟩ : D) ∈ (S : Subgroup J).subgroupOf D from hx.1)
  rw [h.cartan_preserves a ha, he'] at hm
  exact ⟨hm, (MulAut.conjNormal b (⟨x, hx.2⟩ : D)).property⟩

/-- The actual N_S(B) action on B/Φ(B) in the Ree alternative of A.3.15(5).
Universal inner–field coverage is the only extra premise beyond the source
configuration; field separation, common coordinates, and normalization are
proved above. The unused SQTK and BS = SB ambient hypotheses are unnecessary
once the raw Cartan configuration has been supplied. -/
theorem frattini_power_of_raw_cartan (hD : generalizedFitting J = D)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hB : IsPGroup p B) (hBD : B ≤ D)
    (h : RawCartan D d e S B n f F H I)
    (hcover : ∀ a : MulAut d.fixedGroup, ∃ (g : d.fixedGroup) (k : ℤ),
      a = MulAut.conj g * d.fieldAutomorphism ^ k) :
    ∀ (s : ((S : Subgroup J) ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  exact frattini_power_of_normalizes D B hD S hp hB
    (normalizes_sylow D h hBD hcover) d e hcover

end Source

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Ree
