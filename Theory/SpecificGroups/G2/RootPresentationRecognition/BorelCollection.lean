module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.ModelRelations
public import Theory.AtlasPort.LinearGroups.G2.Borel

/-!
# Borel collection and rank-one exchange from the G₂ equations

The positive collector and torus normalization put the generated Borel into
six-root-times-torus form. Removing the simple-root coordinate leaves a
five-root radical, which the corresponding reflection sends into the Borel.
The two rank-one exchange identities retain their distinct full coroots.
All proofs use only the stated equations and apply to the abstract presentation.

This supplies the local steps of the Bruhat argument for the finite split
G₂ comparison in DGS, Groups and Graphs, Theorem D, p.224. The polynomial
coordinates are those of the licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
namespace Atlas.G2.RootPresentationRecognition.BorelWeylData
variable {F G : Type*} [Field F] [CharP F 2] [Group G]
  (d : BorelWeylData F G) (R : d.Relations)

def borel : Subgroup G := d.toPositiveRoots.generated ⊔ d.torus.range

include R
omit [CharP F 2] in
theorem torus_product (p : Fˣ × Fˣ) (t : Fin 6 → F) :
    d.torus p * d.product t * (d.torus p)⁻¹ =
      d.product (fun i => weight p.1 p.2 i * t i) := by
  change (MulAut.conj (d.torus p)) (d.product t) = _
  simp only [PositiveRoots.product, map_mul, MulAut.conj_apply, R.torus_root]

theorem torus_normalizes {t u : G} (ht : t ∈ d.torus.range)
    (hu : u ∈ d.toPositiveRoots.generated) :
    t * u * t⁻¹ ∈ d.toPositiveRoots.generated := by
  obtain ⟨p,rfl⟩ := ht
  obtain ⟨a,rfl⟩ := (d.toPositiveRoots.mem_generated_iff R.toCharTwoRelations.collection u).mp hu
  rw [torus_product d R]
  exact d.toPositiveRoots.product_mem_generated _

private def borelRange : Subgroup G where
  carrier := {g | ∃ u ∈ d.toPositiveRoots.generated, ∃ t ∈ d.torus.range, g = u*t}
  one_mem' := ⟨1,Subgroup.one_mem _,1,Subgroup.one_mem _,by simp⟩
  mul_mem' := by
    rintro x y ⟨u,hu,t,ht,rfl⟩ ⟨v,hv,s,hs,rfl⟩
    refine ⟨u*(t*v*t⁻¹), Subgroup.mul_mem _ hu (torus_normalizes d R ht hv),
      t*s,Subgroup.mul_mem _ ht hs,?_⟩
    group
  inv_mem' := by
    rintro x ⟨u,hu,t,ht,rfl⟩
    refine ⟨t⁻¹*u⁻¹*(t⁻¹)⁻¹,
      torus_normalizes d R (Subgroup.inv_mem _ ht) (Subgroup.inv_mem _ hu),
      t⁻¹,Subgroup.inv_mem _ ht,?_⟩
    group

private theorem borel_eq_range : d.borel = borelRange d R := by
  apply le_antisymm
  · apply sup_le
    · intro u hu
      exact ⟨u,hu,1,Subgroup.one_mem _,by simp⟩
    · intro t ht
      exact ⟨1,Subgroup.one_mem _,t,ht,by simp⟩
  · rintro g ⟨u,hu,t,ht,rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ht)

theorem mem_borel_iff (g : G) :
    g ∈ d.borel ↔ ∃ (a : Fin 6 → F) (p : Fˣ × Fˣ), g = d.product a * d.torus p := by
  rw [borel_eq_range d R]
  constructor
  · rintro ⟨u,hu,t,⟨p,rfl⟩,rfl⟩
    obtain ⟨a,rfl⟩ := (d.toPositiveRoots.mem_generated_iff R.toCharTwoRelations.collection u).mp hu
    exact ⟨a,p,rfl⟩
  · rintro ⟨a,p,rfl⟩
    exact ⟨d.product a,d.toPositiveRoots.product_mem_generated a,d.torus p,⟨p,rfl⟩,rfl⟩

omit R [CharP F 2] in
theorem root_mem_borel (i : Fin 6) (a : F) : d.x i a ∈ d.borel :=
  Subgroup.mem_sup_left (d.toPositiveRoots.root_mem_generated i a)

omit R [CharP F 2] in
theorem torus_mem_borel (p : Fˣ × Fˣ) : d.torus p ∈ d.borel :=
  Subgroup.mem_sup_right ⟨p,rfl⟩

omit [CharP F 2] in
theorem r_inv : d.r⁻¹ = d.r := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using R.r_sq)
omit [CharP F 2] in
theorem s_inv : d.s⁻¹ = d.s := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using R.s_sq)

omit R in
theorem root_inv (i : Fin 6) (a : F) : (d.x i a)⁻¹ = d.x i a := by
  apply inv_eq_of_mul_eq_one_left
  rw [← PositiveRoots.x_add, CharTwo.add_self_eq_zero, PositiveRoots.x_zero]

/-- Rank-one exchange, with the full torus factor retained. -/
theorem long_exchange (a : Fˣ) :
    d.r * d.x 4 (a:F) * d.r =
      d.x 4 (↑a⁻¹:F) * d.torus (1,a⁻¹) * d.r * d.x 4 (↑a⁻¹:F) := by
  have h := R.long_word a⁻¹
  simp only [inv_inv, r_inv d R] at h
  calc
    _ = (d.x 4 (↑a⁻¹:F))⁻¹ *
      (d.x 4 (↑a⁻¹:F) * (d.r * d.x 4 (a:F) * d.r) * d.x 4 (↑a⁻¹:F)) *
      (d.x 4 (↑a⁻¹:F))⁻¹ := by group
    _ = _ := by rw [h, root_inv]; simp only [mul_assoc]

/-- The short-root exchange has its distinct coroot. -/
theorem short_exchange (a : Fˣ) :
    d.s * d.x 5 (a:F) * d.s =
      d.x 5 (↑a⁻¹:F) * d.torus (a⁻¹,a) * d.s * d.x 5 (↑a⁻¹:F) := by
  have h := R.short_word a⁻¹
  simp only [inv_inv, s_inv d R] at h
  calc
    _ = (d.x 5 (↑a⁻¹:F))⁻¹ *
      (d.x 5 (↑a⁻¹:F) * (d.s * d.x 5 (a:F) * d.s) * d.x 5 (↑a⁻¹:F)) *
      (d.x 5 (↑a⁻¹:F))⁻¹ := by group
    _ = _ := by rw [h, root_inv]; simp only [mul_assoc]


/-- `false` is the long reflection and `true` the short reflection. -/
def reflection (short : Bool) : G := if short then d.s else d.r

def simpleRoot (short : Bool) : Fin 6 := if short then 5 else 4

def rootPermutation (short : Bool) : Fin 6 → Fin 6 :=
  if short then ![0,4,3,2,1,5] else ![1,0,2,5,4,3]

omit [CharP F 2] in
theorem reflection_inv (short : Bool) : (d.reflection short)⁻¹ = d.reflection short := by
  cases short
  · exact r_inv d R
  · exact s_inv d R

omit [CharP F 2] in
theorem reflection_sq (short : Bool) : d.reflection short * d.reflection short = 1 := by
  cases short
  · exact (pow_two d.r).symm.trans R.r_sq
  · exact (pow_two d.s).symm.trans R.s_sq

omit [CharP F 2] in
theorem reflection_root (short : Bool) (i : Fin 6) (hi : i ≠ simpleRoot short) (a : F) :
    d.reflection short * d.x i a * (d.reflection short)⁻¹ =
      d.x (rootPermutation short i) a := by
  cases short <;> fin_cases i
  · exact R.rA a
  · exact R.rB a
  · exact R.rC a
  · exact R.rD a
  · exact (hi rfl).elim
  · exact R.rF a
  · exact R.sA a
  · exact R.sB a
  · exact R.sC a
  · exact R.sD a
  · exact R.sE a
  · exact (hi rfl).elim

omit [CharP F 2] in
theorem reflection_torus_mem (short : Bool) (p : Fˣ × Fˣ) :
    d.reflection short * d.torus p * (d.reflection short)⁻¹ ∈ d.borel := by
  cases short
  · change d.r * d.torus p * d.r⁻¹ ∈ d.borel
    rw [R.r_torus]
    exact torus_mem_borel d _
  · change d.s * d.torus p * d.s⁻¹ ∈ d.borel
    rw [R.s_torus]
    exact torus_mem_borel d _

omit [CharP F 2] in
theorem reflection_radical_mem (short : Bool) (t : Fin 6 → F) (ht : t (simpleRoot short) = 0) :
    d.reflection short * d.product t * (d.reflection short)⁻¹ ∈ d.borel := by
  have hx (i : Fin 6) :
      (MulAut.conj (d.reflection short)) (d.x i (t i)) ∈ d.borel := by
    by_cases hi : i = simpleRoot short
    · simp only [hi, ht, PositiveRoots.x_zero, map_one]
      exact Subgroup.one_mem _
    · change d.reflection short * d.x i (t i) * (d.reflection short)⁻¹ ∈ d.borel
      rw [reflection_root d R short i hi]
      exact root_mem_borel d _ _
  change (MulAut.conj (d.reflection short)) (d.product t) ∈ d.borel
  simp only [PositiveRoots.product, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hx 0) (hx 1)) (hx 2)) (hx 3)) (hx 4)) (hx 5)

/-- Isolate the simple root on the right; the other five roots are absorbed
by the Borel after reflection. -/
theorem reflection_borel (short : Bool) (b : G) (hb : b ∈ d.borel) :
    ∃ (c : G) (a : F), c ∈ d.borel ∧
      d.reflection short * b = c * d.reflection short * d.x (simpleRoot short) a := by
  obtain ⟨t,p,rfl⟩ := (mem_borel_iff d R b).mp hb
  let i := simpleRoot short
  let u := unipotentProductParameters t (Pi.single i (t i))
  have hu : u i = 0 := by
    cases short <;> simp [u,i,simpleRoot,unipotentProductParameters,CharTwo.add_self_eq_zero]
  have hprod : d.product u = d.product t * d.x i (t i) := by
    rw [← R.toCharTwoRelations.collection.product_mul, PositiveRoots.product_single]
  let w := d.reflection short
  let a := weight p⁻¹.1 p⁻¹.2 i * t i
  have htor : (d.torus p)⁻¹ * d.x i (t i) * d.torus p = d.x i a := by
    have hh := R.torus_root p⁻¹.1 p⁻¹.2 i (t i)
    simpa only [Prod.mk.eta, map_inv, inv_inv] using hh
  refine ⟨(w * d.product u * w⁻¹) * (w * d.torus p * w⁻¹), a,
    Subgroup.mul_mem _ (reflection_radical_mem d R short u hu)
      (reflection_torus_mem d R short p), ?_⟩
  dsimp only [w]
  rw [← htor, hprod]
  have hxx : d.x i (t i) * d.x i (t i) = 1 := by
    rw [← PositiveRoots.x_add, CharTwo.add_self_eq_zero, PositiveRoots.x_zero]
  group
  rw [mul_assoc (d.reflection short * d.product t), hxx, mul_one]

end Atlas.G2.RootPresentationRecognition.BorelWeylData
