module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.Catalogue
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CatalogueCoverage.Extensions
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CatalogueCoverage.Faithfulness
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CatalogueCoverage.ActorComparison
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CatalogueCoverage.FiniteChecks

/-!
# From finite elementary extensions to the literal actor catalogue

A largest-row argument proves completeness from checks of adjoining commuting
involutions. Conjugating that row onto the subsequence products of a catalogue
list identifies the actual subgroup closure. The number of subsequence products
is at most two to the list length, giving the required binary-rank comparison.

The imported leaves prove finite code arithmetic, faithfulness, multiplication
compatibility, coverage of `standardActors` by codes, and the finite extension
and conjugacy certificates. `standardCatalogue_cover` assembles them to cover
every nontrivial elementary subgroup by the sixty actual catalogue subgroups,
discharging the coverage premise of `standardActors_gap_of_catalogue_cover`.

Source: Guralnick–Malle, Classification of 2F-modules II, Lemma 4.5 and
Proposition 4.8 step 3A; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
set_option backward.isDefEq.respectTransparency false

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
open CoverageCode

section Generic
variable {G : Type*} [_root_.Group G]

private theorem actor_inv
    (f : Code → G) (f_zero : f 0 = 1)
    (hmul : ∀ a b, f (CoverageCode.mul a b) = f a * f b)
    (c : Code) : f (CoverageCode.inv c) = (f c)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hmul, CoverageCode.inv_mul, f_zero]

private theorem actor_conj
    (f : Code → G) (f_zero : f 0 = 1)
    (hmul : ∀ a b, f (CoverageCode.mul a b) = f a * f b)
    (g c : Code) : f (CoverageCode.conj g c) =
      MulAut.conj (f g) (f c) := by
  simp only [CoverageCode.conj, hmul, actor_inv f f_zero hmul, MulAut.conj_apply]

private theorem actor_products_mem
    (f : Code → G) (f_zero : f 0 = 1)
    (hmul : ∀ a b, f (CoverageCode.mul a b) = f a * f b)
    (H : Subgroup G) (l : List Code)
    (hl : ∀ c ∈ l, f c ∈ H) :
    ∀ c ∈ products 0 CoverageCode.mul l, f c ∈ H := by
  induction l with
  | nil =>
    intro c hc
    have hc0 : c = 0 := by simpa [products] using hc
    simp [hc0, f_zero]
  | cons a l ih =>
    have htail := ih (fun c hc => hl c (List.mem_cons_of_mem a hc))
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact htail c hc
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
      rw [hmul]
      exact H.mul_mem (hl a (List.mem_cons_self)) (htail b hb)

private theorem subgroup_eq_closure_of_products
    (f : Code → G) (f_zero : f 0 = 1)
    (hmul : ∀ a b, f (CoverageCode.mul a b) = f a * f b)
    (H : Subgroup G) (l : List Code)
    (hH : ∀ x, x ∈ H ↔ ∃ c ∈ products 0 CoverageCode.mul l, f c = x) :
    H = Subgroup.closure (f '' {c | c ∈ l}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := (hH x).mp hx
    exact actor_products_mem f f_zero hmul (Subgroup.closure (f '' {c | c ∈ l})) l
      (fun c hc => Subgroup.subset_closure ⟨c, hc, rfl⟩) c hc
  · rw [Subgroup.closure_le]
    rintro x ⟨c, hc, rfl⟩
    exact (hH _).mpr ⟨c, mem_products_of_mem 0 CoverageCode.mul CoverageCode.mul_zero hc, rfl⟩

private theorem rank_le_of_products
    (f : Code → G)
    (H : Subgroup G) (l : List Code)
    (hH : ∀ x, x ∈ H ↔ ∃ c ∈ products 0 CoverageCode.mul l, f c = x) :
    rank H ≤ l.length := by
  let liftCode : (products 0 CoverageCode.mul l) → H := fun c =>
    ⟨f c.val, (hH _).mpr ⟨c.val, c.property, rfl⟩⟩
  have hf : Function.Surjective liftCode := by
    intro x
    obtain ⟨c, hc, he⟩ := (hH x.val).mp x.property
    exact ⟨⟨c, hc⟩, Subtype.ext he⟩
  have hc : Nat.card H ≤ (products 0 CoverageCode.mul l).card := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
      Nat.card_le_card_of_surjective liftCode hf
  have h := Nat.log_mono_right (b := 2) (hc.trans (card_products_le 0 CoverageCode.mul l))
  exact h.trans_eq (Nat.log_pow (by decide : 1 < 2) l.length)

private theorem elementary_codes_have_row
    (f : Code → G) (f_zero : f 0 = 1)
    (hmul : ∀ a b, f (CoverageCode.mul a b) = f a * f b)
    (hinj : Function.Injective f)
    (rows : Fin 241 → Finset Code) (hbase : rows 0 = {0})
    (hzero : ∀ i, 0 ∈ rows i)
    (hext : ∀ i c, CoverageCode.mul c c = 0 →
      (∀ a ∈ rows i, CoverageCode.mul c a = CoverageCode.mul a c) →
      ∃ j, rows j = rows i ∪ (rows i).image (CoverageCode.mul c))
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) :
    ∃ k, ∀ c, c ∈ rows k ↔ f c ∈ A := by
  classical
  let : IsElementaryAbelian 2 A := hA
  let T := Finset.univ.filter (fun c => f c ∈ A)
  have hT (c : Code) : c ∈ T ↔ f c ∈ A := by simp [T]
  have h0 : (0 : Code) ∈ T := (hT 0).mpr (by simpa only [f_zero] using A.one_mem)
  have hclosed : ∀ x ∈ T, ∀ y ∈ T, CoverageCode.mul x y ∈ T := by
    intro x hx y hy
    apply (hT _).mpr
    rw [hmul]
    exact A.mul_mem ((hT x).mp hx) ((hT y).mp hy)
  have hsq : ∀ x ∈ T, CoverageCode.mul x x = 0 := by
    intro x hx
    apply hinj
    rw [hmul, f_zero, ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian _ ((hT x).mp hx)
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, CoverageCode.mul x y = CoverageCode.mul y x := by
    intro x hx y hy
    apply hinj
    simp only [hmul]
    exact congrArg Subtype.val (mul_comm' (⟨f x, (hT x).mp hx⟩ : A)
      (⟨f y, (hT y).mp hy⟩ : A))
  have hrows : ∃ k : Fin 241, rows k = T := by
    exact exists_row_of_extensions (C := Code) (I := Fin 241) 0 CoverageCode.mul rows 0
      hbase hzero CoverageCode.mul_zero hext T h0 hclosed hsq hcomm
  obtain ⟨k, hk⟩ := hrows
  exact ⟨k, fun c => by rw [hk]; exact hT c⟩

/-- The concrete model comparison and local extension checks suffice for the
literal normalizer catalogue. The finite certificates remain explicit here. -/
private theorem catalogue_cover_of_extensions
    (f : Code → G) (f_zero : f 0 = 1) (S : Subgroup G)
    (hmul : ∀ a b, f (CoverageCode.mul a b) = f a * f b)
    (hinj : Function.Injective f)
    (hcover : ∀ x ∈ S, ∃ c, f c = x)
    (rows : Fin 241 → Finset Code) (hbase : rows 0 = {0})
    (hzero : ∀ i, 0 ∈ rows i)
    (hext : ∀ i c, CoverageCode.mul c c = 0 →
      (∀ a ∈ rows i, CoverageCode.mul c a = CoverageCode.mul a c) →
      ∃ j, rows j = rows i ∪ (rows i).image (CoverageCode.mul c))
    (hreps : ∀ i, rows i ≠ {0} → ∃ (j : Fin 60) (g : Code),
      (rows i).image (CoverageCode.conj g) = products 0 CoverageCode.mul (catalogueGenerators j))
    (A : Subgroup G) (hAS : A ≤ S)
    (hA : IsElementaryTwo A) :
    ∃ (i : Fin 60) (g : G),
      A.map (MulAut.conj g).toMonoidHom = Subgroup.closure (f '' {c | c ∈ catalogueGenerators i}) ∧
        rank A ≤ (catalogueGenerators i).length := by
  classical
  have hrow : ∃ k : Fin 241, ∀ c : Code, c ∈ rows k ↔ f c ∈ A :=
    elementary_codes_have_row f f_zero hmul hinj rows hbase hzero hext A hA.2
  obtain ⟨k, hk⟩ := hrow
  have hk0 : rows k ≠ {0} := by
    intro he
    apply hA.1
    apply le_antisymm _ bot_le
    intro a ha
    have hcode : ∃ c : Code, f c = a := hcover a (hAS ha)
    obtain ⟨c, hc⟩ := hcode
    subst a
    have hc : c ∈ rows k := (hk c).mpr ha
    have hc0 : c = 0 := by simpa only [he, Finset.mem_singleton] using hc
    exact Subgroup.mem_bot.mpr ((congrArg f hc0).trans f_zero)
  obtain ⟨i, g, hg⟩ := hreps k hk0
  let H := A.map (MulAut.conj (f g)).toMonoidHom
  have hH : ∀ x, x ∈ H ↔
      ∃ c ∈ products 0 CoverageCode.mul (catalogueGenerators i), f c = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      have hcode : ∃ c : Code, f c = a := hcover a (hAS ha)
      obtain ⟨c, hc⟩ := hcode
      subst a
      refine ⟨CoverageCode.conj g c, ?_, actor_conj f f_zero hmul g c⟩
      rw [← hg]
      exact Finset.mem_image.mpr ⟨c, (hk c).mpr ha, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      rw [← hg] at hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      rw [actor_conj f f_zero hmul]
      exact Subgroup.mem_map.mpr ⟨f a, (hk a).mp ha, rfl⟩
  refine ⟨i, f g, subgroup_eq_closure_of_products f f_zero hmul H _ hH, ?_⟩
  have hr := rank_le_of_products f H _ hH
  rwa [rank_map_conj] at hr

end Generic

/-- The concrete model comparison and local extension checks suffice for the
literal normalizer catalogue. The finite certificates remain explicit here. -/
theorem standardCatalogue_cover_of_extensions
    (hmul : ∀ a b, codeActor (CoverageCode.mul a b) = codeActor a * codeActor b)
    (hcover : ∀ x ∈ standardActors, ∃ c, codeActor c = x)
    (rows : Fin 241 → Finset Code) (hbase : rows 0 = {0})
    (hzero : ∀ i, 0 ∈ rows i)
    (hext : ∀ i c, CoverageCode.mul c c = 0 →
      (∀ a ∈ rows i, CoverageCode.mul c a = CoverageCode.mul a c) →
      ∃ j, rows j = rows i ∪ (rows i).image (CoverageCode.mul c))
    (hreps : ∀ i, rows i ≠ {0} → ∃ (j : Fin 60) (g : Code),
      (rows i).image (CoverageCode.conj g) = products 0 CoverageCode.mul (catalogueGenerators j))
    (A : Subgroup (linearNormalizer adjoint)) (hAS : A ≤ standardActors)
    (hA : IsElementaryTwo A) :
    ∃ (i : Fin 60) (g : linearNormalizer adjoint),
      A.map (MulAut.conj g).toMonoidHom = catalogueSubgroup i ∧
        rank A ≤ (catalogueGenerators i).length := by
  exact catalogue_cover_of_extensions codeActor codeActor_zero standardActors hmul codeActor_injective hcover
    rows hbase hzero hext hreps A hAS hA

/-- Every nontrivial elementary subgroup of the standard adjoint actors is
conjugate to an actual catalogue subgroup, with rank bounded by the length of
its generator list. The rank-four hypothesis matches the fixed-space consumer;
the finite extension proof already covers all elementary subgroups. -/
theorem standardCatalogue_cover
    (A : Subgroup (linearNormalizer adjoint)) (hAS : A ≤ standardActors)
    (hA : IsElementaryTwo A) (_hr : rank A ≤ 4) :
    ∃ (i : Fin 60) (g : linearNormalizer adjoint),
      A.map (MulAut.conj g).toMonoidHom = catalogueSubgroup i ∧
        rank A ≤ (catalogueGenerators i).length := by
  exact standardCatalogue_cover_of_extensions codeActor_mul codeActor_cover
    elementaryRows elementaryRows_zero zero_mem_elementaryRows
    elementaryRows_extend elementaryRows_conjugate A hAS hA

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
