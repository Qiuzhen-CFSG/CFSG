module

public import Theory.SpecificGroups.PSL2.PrimePerfectCore
public import Theory.SpecificGroups.PGL2.PerfectCentralizer
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.GroupAction.PerfectFrattiniAction
public import Theory.Frattini.PGroup

/-!
# Perfect section factors on an odd plane

Two perfect subgroups commuting modulo the first subgroup's two-core cannot
both have nontrivial images in GL₂(p), for an odd prime p. Perfectness puts
the first image in SL₂(p); the prime-field subgroup theorem kills its
two-core in PSL₂(p). The projective images therefore commute, and a
nontrivial perfect subgroup of PGL₂ has trivial centralizer. Perfectness
also kills a scalar image.

The same result applies to actions on finite p-groups with Frattini quotient
of order at most p². Burnside's Frattini kernel theorem lifts triviality
back to the original p-group. Conjugate factors have conjugate action
images, so in this case both actions are trivial.

Source: Aschbacher--Smith, proof of 9.4.1, printed p.736. The two-core
hypothesis retains section commutation and does not assert centrality of
the original core.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups

theorem Matrix.GeneralLinearGroup.perfect_twoCore_le_projective_ker {p : ℕ} [Fact p.Prime] (ho : Odd p)
    {A : Type*} [Group A] [Group.IsPerfect A]
    (f : A →* GL (Fin 2) (ZMod p)) :
    pCore 2 A ≤ (ProjGenLinGroup.mk.comp f).ker := by
  let d := GeneralLinearGroup.det.comp f
  let : Group.IsPerfect d.range := Group.IsPerfect.range d
  have hd (a : A) : d a = 1 :=
    congrArg Subtype.val (Subsingleton.elim (d.rangeRestrict a) 1)
  let s : A →* SL(2,ZMod p) := {
    toFun a := ⟨(f a).val, congrArg Units.val (hd a)⟩
    map_one' := by apply Subtype.ext; exact congrArg Units.val f.map_one
    map_mul' a b := by apply Subtype.ext; exact congrArg Units.val (f.map_mul a b) }
  let q := QuotientGroup.mk' (center SL(2,ZMod p))
  have hk := Theory.PSL2.prime_perfect_hom_twoCore_le_ker ho (Nat.card_zmod p) (q.comp s)
  intro a ha
  have hs : s a ∈ center SL(2,ZMod p) := (QuotientGroup.eq_one_iff _).mp (hk ha)
  rw [← SpecialLinearGroup.toPGL_ker] at hs
  change ProjGenLinGroup.mk (f a) = 1
  have he : SpecialLinearGroup.toGL (s a) = f a := by apply Units.ext; rfl
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (s a)) = 1 at hs
  rwa [he] at hs


private theorem trivial_of_projective_trivial
    {F A : Type*} [Field F] [Group A] [Group.IsPerfect A]
    (f : A →* GL (Fin 2) F) (hf : ProjGenLinGroup.mk.comp f = 1) : f = 1 := by
  have hz (a : A) : f a ∈ center (GL (Fin 2) F) := by
    rw [← ProjGenLinGroup.ker_mk]
    exact DFunLike.congr_fun hf a
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : IsMulCommutative f.range := IsMulCommutative.of_comm (by
    rintro ⟨_,a,rfl⟩ ⟨_,b,rfl⟩
    exact Subtype.ext ((mem_center_iff.mp (hz b)) (f a)))
  apply MonoidHom.ext
  intro a
  exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict a) 1)

theorem Subgroup.perfect_sections_linear_two_trivial
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    {G : Type*} [Group G] (A B : Subgroup G)
    [Group.IsPerfect A] [Group.IsPerfect B]
    (f : G →* GL (Fin 2) (ZMod p))
    (hc : ⁅B,A⁆ ≤ (pCore 2 A).map A.subtype) :
    f.comp A.subtype = 1 ∨ f.comp B.subtype = 1 := by
  let q := ProjGenLinGroup.mk (n := Fin 2) (R := ZMod p)
  let F := q.comp f
  have hk : (pCore 2 A).map A.subtype ≤ F.ker := by
    rintro _ ⟨a,ha,rfl⟩
    exact Matrix.GeneralLinearGroup.perfect_twoCore_le_projective_ker ho (f.comp A.subtype) ha
  have hcomm : ⁅B.map F,A.map F⁆ = ⊥ := by
    rw [← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (hc.trans hk)
  have hcent : B.map F ≤ centralizer (A.map F : Set _) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  by_cases ha : A.map F = ⊥
  · left
    apply trivial_of_projective_trivial
    apply MonoidHom.ext
    intro a
    exact mem_bot.mp (ha ▸ mem_map_of_mem F a.property)
  · right
    let : Group.IsPerfect (A.map F) := Group.IsPerfect.map F
    rw [Theory.PGL2.centralizer_eq_bot_of_perfect _ ha] at hcent
    apply trivial_of_projective_trivial
    apply MonoidHom.ext
    intro b
    exact mem_bot.mp (hcent (mem_map_of_mem F b.property))


theorem Subgroup.perfect_sections_frattini_two_trivial
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    {G Q : Type*} [Group G] [Group Q] [Finite Q]
    (A B : Subgroup G) [Group.IsPerfect A] [Group.IsPerfect B]
    (hQ : IsPGroup p Q) (hd : Nat.card (Q ⧸ frattini Q) ≤ p ^ 2)
    (f : G →* MulAut Q)
    (hc : ⁅B,A⁆ ≤ (pCore 2 A).map A.subtype) :
    f.comp A.subtype = 1 ∨ f.comp B.subtype = 1 := by
  let : Fact (IsPGroup p Q) := ⟨hQ⟩
  let : IsElementaryAbelian p (Q ⧸ frattini Q) := isElementaryAbelian_quotient_frattini
  obtain ⟨e,he⟩ :=
    IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le (Q ⧸ frattini Q) hd
  let u := quotientAut (frattini Q)
  have lift (C : Subgroup G) [Group.IsPerfect C]
      (hc : (e.comp (u.comp f)).comp C.subtype = 1) : f.comp C.subtype = 1 := by
    by_contra hn
    apply MonoidHom.frattini_comp_ne_one_of_isPerfect hQ (f.comp C.subtype) hn
    apply MonoidHom.ext
    intro c
    apply he
    exact (DFunLike.congr_fun hc c).trans e.map_one.symm
  rcases Subgroup.perfect_sections_linear_two_trivial ho A B (e.comp (u.comp f)) hc with h | h
  · exact Or.inl (lift A h)
  · exact Or.inr (lift B h)

theorem Subgroup.perfect_conjugate_section_frattini_two_trivial
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    {G Q : Type*} [Group G] [Group Q] [Finite Q]
    (A : Subgroup G) [Group.IsPerfect A] (t : G)
    (hQ : IsPGroup p Q) (hd : Nat.card (Q ⧸ frattini Q) ≤ p ^ 2)
    (f : G →* MulAut Q)
    (hc : ⁅A.map (MulAut.conj t).toMonoidHom,A⁆ ≤ (pCore 2 A).map A.subtype) :
    f.comp A.subtype = 1 := by
  let B := A.map (MulAut.conj t).toMonoidHom
  let : Group.IsPerfect B := Group.IsPerfect.map _
  rcases Subgroup.perfect_sections_frattini_two_trivial ho A B hQ hd f hc with h | h
  · exact h
  apply MonoidHom.ext
  intro a
  have hb : t * a.val * t⁻¹ ∈ B := mem_map_of_mem (MulAut.conj t).toMonoidHom a.property
  have he := DFunLike.congr_fun h (⟨t * a.val * t⁻¹,hb⟩ : B)
  change f (t * a.val * t⁻¹) = 1 at he
  rw [map_mul,map_mul,map_inv] at he
  exact mul_left_cancel ((mul_inv_eq_one.mp he).trans (mul_one (f t)).symm)
