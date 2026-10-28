module
public import Theory.Mathieu.M12.ExceptionalParabolics
public import Theory.Mathieu.M12.ExceptionalParabolics.SourceRecognitionCoreExtensionBound

/-!
# Recognition of the second M₁₂ endpoint by its normalized core extension

The concrete second parabolic realizes the normalized three-involution core
and its two extension actors. Short words recover the existing five local
generators, proving generation. Applying the order bound to paired generators
in a direct product recognizes any generated realization of order 192.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.12) and its
final identification paragraph, pp.405–406; the model is (3.8), p.390.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
variable {G H : Type*} [Group G] [Group H]

theorem CoreExtensionRelations.prod {x y z a b T C : G} {x' y' z' a' b' T' C' : H}
    (r : CoreExtensionRelations x y z a b T C)
    (q : CoreExtensionRelations x' y' z' a' b' T' C') :
    CoreExtensionRelations (x,x') (y,y') (z,z') (a,a') (b,b') (T,T') (C,C') where
  toRelations := r.toRelations.prod q.toRelations
  T_sq := Prod.ext r.T_sq q.T_sq
  C_cube := Prod.ext r.C_cube q.C_cube
  TC_sq := Prod.ext r.TC_sq q.TC_sq
  Tx := Prod.ext r.Tx q.Tx
  Ty := Prod.ext r.Ty q.Ty
  Tz := Prod.ext r.Tz q.Tz
  Cx := Prod.ext r.Cx q.Cx
  Cy := Prod.ext r.Cy q.Cy
  Cz := Prod.ext r.Cz q.Cz

variable [Finite G] [Finite H]

/-- The extension relations determine every generated realization of order 192. -/
theorem CoreExtensionRelations.equiv_of_card {x y z a b T C : G}
    {x' y' z' a' b' T' C' : H}
    (r : CoreExtensionRelations x y z a b T C)
    (q : CoreExtensionRelations x' y' z' a' b' T' C')
    (hgen : closure ({x,y,z,T,C} : Set G) = ⊤)
    (hgen' : closure ({x',y',z',T',C'} : Set H) = ⊤)
    (hcard : Nat.card G = 192) (hcard' : Nat.card H = 192) :
    Nonempty (G ≃* H) := by
  let D := closure ({(x,x'),(y,y'),(z,z'),(T,T'),(C,C')} : Set (G × H))
  let f : D →* G := (MonoidHom.fst G H).domRestrict D
  let g : D →* H := (MonoidHom.snd G H).domRestrict D
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    dsimp only [f]
    rw [MonoidHom.domRestrict_range]
    dsimp only [D]
    rw [MonoidHom.map_closure]
    simpa only [Set.image_insert_eq, Set.image_singleton, MonoidHom.coe_fst, Prod.fst] using hgen
  have hg : Function.Surjective g := by
    apply MonoidHom.range_eq_top.mp
    dsimp only [g]
    rw [MonoidHom.domRestrict_range]
    dsimp only [D]
    rw [MonoidHom.map_closure]
    simpa only [Set.image_insert_eq, Set.image_singleton, MonoidHom.coe_snd, Prod.snd] using hgen'
  have hd : Nat.card D ≤ 192 := (r.prod q).card_le
  let ef := MulEquiv.ofBijective f (hf.bijective_of_nat_card_le (by simpa only [hcard] using hd))
  let eg := MulEquiv.ofBijective g (hg.bijective_of_nat_card_le (by simpa only [hcard'] using hd))
  exact ⟨ef.symm.trans eg⟩

private theorem extension_leftJ_mem : leftJ ∈ secondParabolic :=
  core_le_secondParabolic ((mem_core _).mpr ⟨.xa 0,.a 0,by decide +kernel⟩)

private theorem extension_leftI_mem : leftI ∈ secondParabolic :=
  core_le_secondParabolic ((mem_core _).mpr ⟨.a 1,.a 0,by decide +kernel⟩)

private theorem extension_rightI_mem : rightI ∈ secondParabolic :=
  core_le_secondParabolic ((mem_core _).mpr ⟨.a 0,.a 1,by decide +kernel⟩)

def extensionX : secondParabolic :=
  ⟨leftI * rightI, mul_mem extension_leftI_mem extension_rightI_mem⟩

def extensionY : secondParabolic :=
  ⟨rightI * movingActor * leftI * movingActor,
    mul_mem (mul_mem (mul_mem extension_rightI_mem movingActor_mem)
      extension_leftI_mem) movingActor_mem⟩

def extensionZ : secondParabolic :=
  ⟨leftJ * extensionY.val, mul_mem extension_leftJ_mem extensionY.property⟩

def extensionA : secondParabolic := ⁅extensionX,extensionY⁆

def extensionB : secondParabolic := ⁅extensionX,extensionZ⁆

def extensionT : secondParabolic := ⟨leftI,extension_leftI_mem⟩

def extensionC : secondParabolic :=
  ⟨leftJ * movingActor ^ 2, mul_mem extension_leftJ_mem (pow_mem movingActor_mem _)⟩

/-- The normalized source relations hold in the concrete second parabolic. -/
theorem extension_relations :
    CoreExtensionRelations extensionX extensionY extensionZ extensionA extensionB
      extensionT extensionC where
  x_sq := by apply Subtype.ext; decide +kernel
  y_sq := by apply Subtype.ext; decide +kernel
  z_sq := by apply Subtype.ext; decide +kernel
  a_order := by apply orderOf_eq_prime <;> decide +kernel
  b_order := by apply orderOf_eq_prime <;> decide +kernel
  a_ne_b := by decide +kernel
  xy := rfl
  xz := rfl
  yz := by apply Subtype.ext; decide +kernel
  bx := by change extensionB * extensionX = extensionX * extensionB; apply Subtype.ext; decide +kernel
  by_ := by change extensionB * extensionY = extensionY * extensionB; apply Subtype.ext; decide +kernel
  bz := by change extensionB * extensionZ = extensionZ * extensionB; apply Subtype.ext; decide +kernel
  T_sq := by apply Subtype.ext; decide +kernel
  C_cube := by apply Subtype.ext; decide +kernel
  TC_sq := by apply Subtype.ext; decide +kernel
  Tx := by apply Subtype.ext; decide +kernel
  Ty := by apply Subtype.ext; decide +kernel
  Tz := by apply Subtype.ext; decide +kernel
  Cx := by apply Subtype.ext; decide +kernel
  Cy := by apply Subtype.ext; decide +kernel
  Cz := by apply Subtype.ext; decide +kernel

private def extensionGenerator (i : Fin 5) : secondParabolic :=
  ![extensionX,extensionY,extensionZ,extensionT,extensionC] i

private def extensionEvaluate : List (Fin 5) → secondParabolic
  | [] => 1
  | i :: w => extensionGenerator i * extensionEvaluate w

private def extensionOldGeneratorWord (i : Fin 5) : List (Fin 5) :=
  ![[3], [2,1], [0,3,3,3], [1,0,2,0], [1,0,4,4]] i

private theorem extensionOldGenerator_eq_word (i : Fin 5) :
    SylowEnumeration.localGenerator i =
      (extensionEvaluate (extensionOldGeneratorWord i) : M12) := by
  fin_cases i <;> decide +kernel

/-- The normalized generators generate the whole second parabolic. -/
theorem extension_generation :
    closure ({extensionX,extensionY,extensionZ,extensionT,extensionC} : Set secondParabolic) = ⊤ := by
  let C := closure ({extensionX,extensionY,extensionZ,extensionT,extensionC} : Set secondParabolic)
  have hs (i : Fin 5) : extensionGenerator i ∈ C := by
    fin_cases i <;> exact subset_closure (by simp [extensionGenerator])
  have hw (w : List (Fin 5)) : extensionEvaluate w ∈ C := by
    induction w with
    | nil => exact C.one_mem
    | cons i w ih => exact C.mul_mem (hs i) ih
  have ho (i : Fin 5) : SylowEnumeration.localGenerator i ∈ C.map secondParabolic.subtype := by
    rw [extensionOldGenerator_eq_word]
    exact mem_map.mpr ⟨_,hw _,rfl⟩
  have hold (w : List (Fin 5)) : SylowEnumeration.localWord w ∈ C.map secondParabolic.subtype := by
    induction w with
    | nil => exact (C.map secondParabolic.subtype).one_mem
    | cons i w ih => exact (C.map secondParabolic.subtype).mul_mem (ho i) ih
  apply top_unique
  intro g _
  have hm : (g : M12).val ∈ SylowEnumeration.wordCarrier :=
    (SylowEnumeration.mem_wordCarrier_iff _).mpr
      ⟨(SylowEnumeration.mem_M12_iff_preservesBlocks _).mp g.val.property,
        (SylowEnumeration.mem_secondParabolic_iff _).mp g.property⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
  have hi' : SylowEnumeration.wordElement i = (g : M12) := Subtype.ext hi
  have hg : (g : M12) ∈ C.map secondParabolic.subtype := hi' ▸ hold _
  obtain ⟨u, hu, he⟩ := mem_map.mp hg
  exact (Subtype.ext he : u = g) ▸ hu

/-- Recognition of the second endpoint from its normalized source relations
and the source lower bound on its order. -/
theorem secondParabolic_equiv_of_coreExtension_relations
    {G : Type*} [Group G] [Finite G] (x y z a b T C : G)
    (r : CoreExtensionRelations x y z a b T C)
    (hgen : closure ({x,y,z,T,C} : Set G) = ⊤) (hcard : 192 ≤ Nat.card G) :
    Nonempty (G ≃* secondParabolic) := by
  have hbound : Nat.card G ≤ 192 := by
    simpa only [hgen, card_top] using r.card_le
  exact r.equiv_of_card extension_relations hgen extension_generation
    (Nat.le_antisymm hbound hcard) card_secondParabolic

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
