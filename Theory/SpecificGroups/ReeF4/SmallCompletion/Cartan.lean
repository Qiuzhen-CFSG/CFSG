module
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations.TorusSeparation
public import Theory.SpecificGroups.ReeF4.SmallCompletion.Native

/-!
# The full Ree Cartan torus on the positive subgroup

The known separating torus actors have surjective commutator maps on each
of the eight literal root blocks, hence no nonidentity fixed point there.
Unique positive block coordinates let us apply this to each coordinate of a
positive element fixed by the whole torus. Thus the positive subgroup has
trivial torus centralizer. Disjointness of the torus and positive subgroup
then makes the torus self-normalizing inside the whole Borel.

Both statements transfer through any injective Borel marking. The separation
calculation retains both coordinates of the nonabelian blocks and covers
q=8. These are the local Cartan inputs for the apartment route; no apartment
alignment or completion recognition is assumed or concluded.

Source: Aschbacher–Smith F.4.10,16, pp.279,282, and GLS3 Table2.4,
Theorem2.4.7(f), `refs/KGroup/GLS3/chapter2.tex`.
-/

public noncomputable section
namespace ReeF4.SmallCompletion
open Subgroup Parabolics ElementaryTwoBound CentralCovers.TwoPrimary
open CentralCovers.TwoPrimary.TailRelations
open scoped Pointwise

private theorem block_fixed_eq_one (m : ℕ) (hm : 0 < m) (j : BlockIndex)
    (x : X m (rootIndex j))
    (hx : ∀ t ∈ fixedTorus m, t * x.val * t⁻¹ = x.val) : x = 1 := by
  have hex : ∃ i : BlockIndex, i ≠ j := by
    by_cases h : j = Sum.inl 0
    · exact ⟨Sum.inl 1, by rw [h]; decide⟩
    · exact ⟨Sum.inl 0,Ne.symm h⟩
  obtain ⟨i,hi⟩ := hex
  obtain ⟨t,ht,hn,_,hs⟩ := torusBlockSeparation m hm i j hi
  let f : X m (rootIndex j) → X m (rootIndex j) := fun z =>
    ⟨t*z.val*t⁻¹*z.val⁻¹, mul_mem ((mem_normalizer_iff.mp (hn j) z.val).mp z.property)
      (inv_mem z.property)⟩
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨z,hz⟩ := hs y
    exact ⟨z,Subtype.ext hz⟩
  apply (Finite.injective_iff_surjective.mpr hsurj)
  apply Subtype.ext
  change t*x.val*t⁻¹*x.val⁻¹ = t*1*t⁻¹*1⁻¹
  rw [hx t ht]
  simp

/-- The full fixed torus has no nonidentity fixed element in the positive group,
including at q=8. -/
theorem unipotent_inf_centralizer_fixedTorus (m : ℕ) (hm : 0 < m) :
    unipotent m ⊓ centralizer (fixedTorus m : Set (Model m)) = ⊥ := by
  apply bot_unique
  rintro x ⟨hx,hc⟩
  obtain ⟨a,ha⟩ := blockProduct_surjective m ⟨x,hx⟩
  have hblocks (t : Model m) (ht : t ∈ fixedTorus m) (i : BlockIndex) :
      t*(a i).val*t⁻¹ = (a i).val := by
    let b : Blocks m := fun i => ⟨t*(a i).val*t⁻¹,
      (mem_normalizer_iff.mp (fixedTorus_normalizes_X m (rootIndex i) ht) _).mp (a i).property⟩
    have he : blockProduct m b = (MulAut.conj t) (blockProduct m a) := by
      simp only [blockProduct,map_mul,map_list_prod,List.map_ofFn]
      rfl
    have hf : (MulAut.conj t) x = x := by
      change t*x*t⁻¹ = x
      rw [hc t ht]
      simp only [mul_assoc,mul_inv_cancel,mul_one]
    have hab : b = a := blockProduct_injective m (he.trans (by rw [ha,hf]))
    exact congrArg (fun z : Blocks m => (z i).val) hab
  have hone : a = 1 := by
    funext i
    exact block_fixed_eq_one m hm i (a i) (fun t ht => hblocks t ht i)
  apply mem_bot.mpr
  change blockProduct m a = x at ha
  rw [←ha,hone]
  simp [blockProduct]

/-- The positive group meets its Cartan torus trivially. -/
theorem unipotent_inf_fixedTorus (m : ℕ) : unipotent m ⊓ fixedTorus m = ⊥ := by
  apply Disjoint.eq_bot
  apply disjoint_of_coprime_natCard
  rw [Parabolics.card_unipotent,←pow_mul]
  exact (Nat.coprime_two_left.mpr
    (Parabolics.fixedTorus_odd_card m (SectionGeometry.BNPair.splitTorus_card_odd m))).pow_left _

/-- No nonidentity positive element normalizes the full fixed torus. -/
theorem unipotent_inf_normalizer_fixedTorus (m : ℕ) (hm : 0 < m) :
    unipotent m ⊓ normalizer (fixedTorus m : Set (Model m)) = ⊥ := by
  apply bot_unique
  rintro x ⟨hx,hn⟩
  apply (unipotent_inf_centralizer_fixedTorus m hm).le
  refine ⟨hx,?_⟩
  intro t ht
  have hU : x*t*x⁻¹*t⁻¹ ∈ unipotent m := by
    have htn : t ∈ normalizer (unipotent m : Set (Model m)) :=
      (fixedTorus_le_borel m).trans (borel_le_unipotent_normalizer m) ht
    have hh := (unipotent m).mul_mem hx ((mem_normalizer_iff.mp htn x⁻¹).mp (inv_mem hx))
    simpa only [mul_assoc] using hh
  have hT : x*t*x⁻¹*t⁻¹ ∈ fixedTorus m :=
    mul_mem ((mem_normalizer_iff.mp hn t).mp ht) (inv_mem ht)
  have he : x*t*x⁻¹*t⁻¹ = 1 := mem_bot.mp ((unipotent_inf_fixedTorus m).le ⟨hU,hT⟩)
  have he' : x*t = t*x := by
    have hh := congrArg (fun z : Model m => z*t*x) he
    simpa only [mul_assoc,inv_mul_cancel_left,one_mul,inv_mul_cancel,mul_one] using hh
  exact he'.symm

/-- The fixed torus is its own normalizer inside the whole native Borel. -/
theorem borel_inf_normalizer_fixedTorus (m : ℕ) (hm : 0 < m) :
    borel m ⊓ normalizer (fixedTorus m : Set (Model m)) = fixedTorus m := by
  apply le_antisymm ?_ (le_inf (fixedTorus_le_borel m) (fixedTorus m).le_normalizer)
  rintro x ⟨hx,hn⟩
  have hprod : x ∈ (unipotent m : Set (Model m)) * (fixedTorus m : Set (Model m)) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _
      ((fixedTorus_le_borel m).trans (borel_le_unipotent_normalizer m)),
      ←SectionGeometry.BNPair.borel_eq_unipotent_sup_fixedTorus]
    exact hx
  obtain ⟨u,hu,t,ht,rfl⟩ := hprod
  have hun : u ∈ normalizer (fixedTorus m : Set (Model m)) := by
    have hh := (normalizer (fixedTorus m : Set (Model m))).mul_mem hn
      ((fixedTorus m).le_normalizer (inv_mem ht))
    simpa only [mul_inv_cancel_right] using hh
  have he : u=1 := mem_bot.mp ((unipotent_inf_normalizer_fixedTorus m hm).le ⟨hu,hun⟩)
  change u*t ∈ fixedTorus m
  rw [he,one_mul]
  exact ht

end ReeF4.SmallCompletion

public noncomputable section
namespace ReeF4.SmallCompletion
open Subgroup Parabolics
variable {m : ℕ} {M : Type*} [Group M]

/-- The no-fixed-point statement survives any faithful marking of the Borel. -/
theorem mapped_unipotent_inf_centralizer_fixedTorus (hm : 0 < m)
    (f : borel m →* M) (hf : Function.Injective f) :
    ((unipotent m).subgroupOf (borel m)).map f ⊓
      centralizer (((fixedTorus m).subgroupOf (borel m)).map f : Set M) = ⊥ := by
  apply bot_unique
  rintro _ ⟨⟨u,hu,rfl⟩,hc⟩
  have hcent : u.val ∈ centralizer (fixedTorus m : Set (Model m)) := by
    intro t ht
    let t' : borel m := ⟨t,fixedTorus_le_borel m ht⟩
    have hh : t'*u = u*t' := hf (by
      rw [map_mul,map_mul]
      exact hc (f t') ⟨t',ht,rfl⟩)
    exact congrArg Subtype.val hh
  have hu1 : u=1 := Subtype.ext (mem_bot.mp
    ((unipotent_inf_centralizer_fixedTorus m hm).le ⟨hu,hcent⟩))
  exact mem_bot.mpr (by rw [hu1,map_one])

/-- The torus remains self-normalizing inside the marked Borel image. -/
theorem mapped_borel_inf_normalizer_fixedTorus (hm : 0 < m)
    (f : borel m →* M) (hf : Function.Injective f) :
    f.range ⊓ normalizer (((fixedTorus m).subgroupOf (borel m)).map f : Set M) =
      ((fixedTorus m).subgroupOf (borel m)).map f := by
  let T := (fixedTorus m).subgroupOf (borel m)
  have hT : normalizer (T : Set (borel m)) = T := by
    rw [←subgroupOf_normalizer_eq (fixedTorus_le_borel m)]
    ext t
    exact ⟨fun ht => (borel_inf_normalizer_fixedTorus m hm).le ⟨t.property,ht⟩,
      fun ht => (fixedTorus m).le_normalizer ht⟩
  apply le_antisymm ?_ (le_inf (map_le_range f T) (T.map f).le_normalizer)
  rintro _ ⟨⟨b,rfl⟩,hn⟩
  have hb : b ∈ (normalizer (T.map f : Set M)).comap f := hn
  rw [comap_normalizer_eq_of_le_range (map_le_range f T),
    comap_map_eq_self_of_injective hf,hT] at hb
  exact ⟨b,hb,rfl⟩

end ReeF4.SmallCompletion

