module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Coordinates
public import Theory.Representation.PSL3Two.NaturalOrbits

/-!
# The two involution orbits in the original full module

The specified natural SL₃(2) coordinates make each moved factor transitive
on its nonidentity elements. Each component centralizes the other factor,
so the original component orbit L₀ is transitive on diagonal vectors.
The exchange and the first natural action make M transitive on pure vectors.
Disjoint commuting factor multiplication exhausts the full module.

Source: Aschbacher--Smith, 10.3.2, first paragraph, printed p.756,
PDF p.773 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Fusion
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreeSurvivor T D)

/-- A vector belonging to one of the two literal moved factors. -/
def Pure (x : G) : Prop := x ∈ ⁅D.fullModule,L⁆ ∨
  x ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom

/-- A product with both literal factor coordinates nonidentity. -/
def Diagonal (x : G) : Prop := ∃ a ∈ ⁅D.fullModule,L⁆,
  ∃ b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom,
  a ≠ 1 ∧ b ≠ 1 ∧ x = a * b

include s

/-- Lift natural SL₃(2) transitivity through the original quotient and coordinates. -/
theorem moved_transitive
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {a c : G} (ha : a ∈ ⁅D.fullModule,L⁆) (hc : c ∈ ⁅D.fullModule,L⁆)
    (han : a ≠ 1) (hcn : c ≠ 1) :
    ∃ l ∈ L, MulAut.conj l a = c := by
  let e := movedCoordinates s hz
  have ha0 : (s.natural.coordinates ⟨a,ha⟩).toAdd ≠ 0 := by
    intro h
    have he : e ⟨a,ha⟩ = e 1 := h.trans e.map_one.symm
    exact han (congrArg Subtype.val (e.injective he))
  have hc0 : (s.natural.coordinates ⟨c,hc⟩).toAdd ≠ 0 := by
    intro h
    have he : e ⟨c,hc⟩ = e 1 := h.trans e.map_one.symm
    exact hcn (congrArg Subtype.val (e.injective he))
  obtain ⟨g,hg⟩ := BinaryLinearThree.natural_transitive_nonzero _ _ ha0 hc0
  obtain ⟨q,rfl⟩ := s.quotient.surjective g
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  refine ⟨l,l.property,?_⟩
  have he := (s.natural.equivariant l ⟨a,ha⟩).trans hg
  exact congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective he))

/-- The conjugate component is transitive on the exchanged factor. -/
theorem partner_transitive
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {b d : G}
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (hd : d ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (hbn : b ≠ 1) (hdn : d ≠ 1) :
    ∃ k ∈ L.map (MulAut.conj s.exchange).toMonoidHom, MulAut.conj k b = d := by
  obtain ⟨a,ha,rfl⟩ := hb
  obtain ⟨c,hc,rfl⟩ := hd
  obtain ⟨l,hl,he⟩ := moved_transitive s hz ha hc
    (fun h => hbn (by simp [h])) (fun h => hdn (by simp [h]))
  refine ⟨MulAut.conj s.exchange l,mem_map_of_mem _ hl,?_⟩
  change (MulAut.conj s.exchange l) * (MulAut.conj s.exchange a) *
    (MulAut.conj s.exchange l)⁻¹ = MulAut.conj s.exchange c
  change l * a * l⁻¹ = c at he
  simpa only [map_mul, map_inv] using congrArg (MulAut.conj s.exchange) he

/-- The original L₀ conjugates any two diagonal vectors. -/
theorem diagonal_transitive
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {x y : G} (hx : Diagonal s x) (hy : Diagonal s y) :
    ∃ l ∈ localOrbit T L, MulAut.conj l x = y := by
  obtain ⟨a,ha,b,hb,han,hbn,rfl⟩ := hx
  obtain ⟨c,hc,d,hd,hcn,hdn,rfl⟩ := hy
  obtain ⟨l,hl,he⟩ := moved_transitive s hz ha hc han hcn
  obtain ⟨k,hk,hf⟩ := partner_transitive s hz hb hd hbn hdn
  have hlf : MulAut.conj l b = b := by
    change l * b * l⁻¹ = b
    rw [s.crossed hb l hl, mul_inv_cancel_right]
  have hkf : MulAut.conj k c = c := by
    change k * c * k⁻¹ = c
    rw [moved_centralizes_partner_component s hc k hk, mul_inv_cancel_right]
  refine ⟨k*l,(localOrbit T L).mul_mem ?_ (le_componentOrbit L T hl),?_⟩
  · rw [orbit_eq_pair s]
    exact mem_sup_right hk
  · calc
      MulAut.conj (k*l) (a*b) = MulAut.conj k (MulAut.conj l (a*b)) := by
        simp [MulAut.conj_apply,mul_assoc]
      _ = c*d := by rw [map_mul,he,hlf,map_mul,hkf,hf]

/-- The original maximal local group preserves the pure vectors. -/
theorem pure_conj {x g : G} (hx : Pure s x) (hg : g ∈ D.maximalLocal) :
    Pure s (MulAut.conj g x) := by
  rcases hx with hx | hx
  · have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rcases survivor_moved_pair s g hg with h | h
    · exact Or.inl (h ▸ hh)
    · exact Or.inr (h ▸ hh)
  · have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rcases partner_pair s g hg with h | h
    · exact Or.inl (h ▸ hh)
    · exact Or.inr (h ▸ hh)

/-- Each pure vector is an M-conjugate of a vector in the first factor. -/
theorem pure_rep {x : G} (hx : Pure s x) :
    ∃ a ∈ ⁅D.fullModule,L⁆, ∃ m ∈ D.maximalLocal, MulAut.conj m a = x := by
  rcases hx with hx | ⟨a,ha,he⟩
  · exact ⟨x,hx,1,D.maximalLocal.one_mem,by simp⟩
  · exact ⟨a,ha,s.exchange,le_normalizer_componentOrbit L T s.exchange_mem,he⟩

/-- The original M conjugates any two nonidentity pure vectors. -/
theorem pure_transitive
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {x y : G} (hx : Pure s x) (hy : Pure s y) (hxn : x ≠ 1) (hyn : y ≠ 1) :
    ∃ m ∈ D.maximalLocal, MulAut.conj m x = y := by
  obtain ⟨a,ha,m,hm,rfl⟩ := pure_rep s hx
  obtain ⟨b,hb,n,hn,rfl⟩ := pure_rep s hy
  obtain ⟨l,hl,he⟩ := moved_transitive s hz ha hb
    (fun h => hxn (by simp [h])) (fun h => hyn (by simp [h]))
  have hlM : l ∈ D.maximalLocal := (localOrbit T L).le_normalizer (le_componentOrbit L T hl)
  refine ⟨n*l*m⁻¹,D.maximalLocal.mul_mem (D.maximalLocal.mul_mem hn hlM)
    (D.maximalLocal.inv_mem hm),?_⟩
  calc
    MulAut.conj (n*l*m⁻¹) (MulAut.conj m a) = MulAut.conj n (MulAut.conj l a) := by
      simp [MulAut.conj_apply,mul_assoc]
    _ = MulAut.conj n b := by rw [he]

/-- The two literal factors exhaust V by pure and diagonal vectors. -/
theorem pure_or_diagonal
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) {x : G} (hx : x ∈ D.fullModule) :
    Pure s x ∨ Diagonal s x := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hc : ⁅D.fullModule,L⁆ ≤ centralizer
      ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom : Set G) := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm
      (⟨b,survivor_partner_le s hb⟩ : D.fullModule) ⟨a,survivor_moved_le s ha⟩)
  have hx' : x ∈ ⁅D.fullModule,L⁆ ⊔
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := s.generated ▸ hx
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _
    (survivor_pair_disjoint s hz) hc
  obtain ⟨⟨a,b⟩,hab⟩ := e.surjective ⟨x,hx'⟩
  have heq : (a:G) * (b:G) = x := (he a b).symm.trans (congrArg Subtype.val hab)
  have ha := a.property
  have hb := b.property
  rw [← heq]
  change Pure s ((a:G)*(b:G)) ∨ Diagonal s ((a:G)*(b:G))
  by_cases han : (a:G) = 1
  · exact Or.inl (Or.inr (by simpa only [han, one_mul] using hb))
  by_cases hbn : (b:G) = 1
  · exact Or.inl (Or.inl (by simpa only [hbn, mul_one] using ha))
  exact Or.inr ⟨a,ha,b,hb,han,hbn,rfl⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Fusion
