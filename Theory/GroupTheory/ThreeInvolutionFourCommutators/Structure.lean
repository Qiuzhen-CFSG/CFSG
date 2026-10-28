module
public import Theory.GroupTheory.ThreeInvolutionFourCommutators

/-!
# Marked recognition of the three-involution group of order thirty-two

The three involutions and their prescribed central commutators determine the
generated group, including its marking. Apply the order-thirty-two calculation
to the diagonal triple in the product of two realizations. Both coordinate
projections are surjective between groups of the same finite order, hence are
isomorphisms.

This supplies the recognition implicit in Goldschmidt, *Automorphisms of
trivalent graphs* (1980), (6.12), printed p.405.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace ThreeInvolutionFourCommutators
variable {G : Type*} {H : Type*} [Group G] [Group H]

/-- The relations of the marked order-thirty-two group. Only the second
commutator's centrality is needed in the order calculation. -/
structure Relations (x y z a b : G) : Prop where
  x_sq : x ^ 2 = 1
  y_sq : y ^ 2 = 1
  z_sq : z ^ 2 = 1
  a_order : orderOf a = 2
  b_order : orderOf b = 2
  a_ne_b : a ≠ b
  xy : ⁅x,y⁆ = a
  xz : ⁅x,z⁆ = b
  yz : ⁅y,z⁆ = a * b
  bx : Commute b x
  by_ : Commute b y
  bz : Commute b z

theorem Relations.card {x y z a b : G} (r : Relations x y z a b) :
    Nat.card (closure ({x,y,z} : Set G)) = 32 :=
  card_closure_eq_thirty_two x y z a b r.x_sq r.y_sq r.z_sq
    r.a_order r.b_order r.a_ne_b r.xy r.xz r.yz r.bx r.by_ r.bz

theorem Relations.prod {x y z a b : G} {x' y' z' a' b' : H}
    (r : Relations x y z a b) (r' : Relations x' y' z' a' b') :
    Relations (x,x') (y,y') (z,z') (a,a') (b,b') where
  x_sq := Prod.ext r.x_sq r'.x_sq
  y_sq := Prod.ext r.y_sq r'.y_sq
  z_sq := Prod.ext r.z_sq r'.z_sq
  a_order := orderOf_eq_prime (Prod.ext
    (r.a_order ▸ pow_orderOf_eq_one a) (r'.a_order ▸ pow_orderOf_eq_one a'))
    (fun he => by
      have h : a = 1 := congrArg Prod.fst he
      have ho := r.a_order
      simp [h] at ho)
  b_order := orderOf_eq_prime (Prod.ext
    (r.b_order ▸ pow_orderOf_eq_one b) (r'.b_order ▸ pow_orderOf_eq_one b'))
    (fun he => by
      have h : b = 1 := congrArg Prod.fst he
      have ho := r.b_order
      simp [h] at ho)
  a_ne_b := fun he => r.a_ne_b (congrArg Prod.fst he)
  xy := Prod.ext r.xy r'.xy
  xz := Prod.ext r.xz r'.xz
  yz := Prod.ext r.yz r'.yz
  bx := Prod.ext r.bx.eq r'.bx.eq
  by_ := Prod.ext r.by_.eq r'.by_.eq
  bz := Prod.ext r.bz.eq r'.bz.eq

private theorem image_triple_closure (f : G →* H) (x y z : G) :
    (closure ({x,y,z} : Set G)).map f = closure ({f x,f y,f z} : Set H) := by
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

/-- Any two realizations are isomorphic with the three generators preserved. -/
theorem Relations.equiv_closure {x y z a b : G} {x' y' z' a' b' : H}
    (r : Relations x y z a b) (r' : Relations x' y' z' a' b') :
    ∃ e : closure ({x,y,z} : Set G) ≃* closure ({x',y',z'} : Set H),
      e ⟨x, subset_closure (by simp)⟩ = ⟨x', subset_closure (by simp)⟩ ∧
      e ⟨y, subset_closure (by simp)⟩ = ⟨y', subset_closure (by simp)⟩ ∧
      e ⟨z, subset_closure (by simp)⟩ = ⟨z', subset_closure (by simp)⟩ := by
  let D := closure ({(x,x'),(y,y'),(z,z')} : Set (G × H))
  let A := closure ({x,y,z} : Set G)
  let B := closure ({x',y',z'} : Set H)
  have hd : Nat.card D = 32 := (r.prod r').card
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [hd]; decide)
  have hf : D.map (MonoidHom.fst G H) = A := image_triple_closure _ _ _ _
  have hg : D.map (MonoidHom.snd G H) = B := image_triple_closure _ _ _ _
  let f : D →* A := ((MonoidHom.fst G H).domRestrict D).codRestrict A
    (fun u => hf ▸ mem_map.mpr ⟨u.val, u.property, rfl⟩)
  let g : D →* B := ((MonoidHom.snd G H).domRestrict D).codRestrict B
    (fun u => hg ▸ mem_map.mpr ⟨u.val, u.property, rfl⟩)
  have hfs : Function.Surjective f := by
    intro u
    have hu : u.val ∈ D.map (MonoidHom.fst G H) := hf.symm ▸ u.property
    obtain ⟨w, hw, he⟩ := mem_map.mp hu
    exact ⟨⟨w,hw⟩, Subtype.ext he⟩
  have hgs : Function.Surjective g := by
    intro u
    have hu : u.val ∈ D.map (MonoidHom.snd G H) := hg.symm ▸ u.property
    obtain ⟨w, hw, he⟩ := mem_map.mp hu
    exact ⟨⟨w,hw⟩, Subtype.ext he⟩
  let ef := MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).mpr
    ⟨hfs, hd.trans r.card.symm⟩)
  let eg := MulEquiv.ofBijective g ((Nat.bijective_iff_surjective_and_card g).mpr
    ⟨hgs, hd.trans r'.card.symm⟩)
  refine ⟨ef.symm.trans eg, ?_, ?_, ?_⟩
  · have he : ef ⟨(x,x'), subset_closure (by simp)⟩ =
        ⟨x, subset_closure (by simp)⟩ := rfl
    change eg (ef.symm _) = _
    rw [← he, ef.symm_apply_apply]
    rfl
  · have he : ef ⟨(y,y'), subset_closure (by simp)⟩ =
        ⟨y, subset_closure (by simp)⟩ := rfl
    change eg (ef.symm _) = _
    rw [← he, ef.symm_apply_apply]
    rfl
  · have he : ef ⟨(z,z'), subset_closure (by simp)⟩ =
        ⟨z, subset_closure (by simp)⟩ := rfl
    change eg (ef.symm _) = _
    rw [← he, ef.symm_apply_apply]
    rfl

end ThreeInvolutionFourCommutators
