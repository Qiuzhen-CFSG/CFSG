module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.CoreGeometry

/-!
# Two generators for the actual second Tits core

The seven positive generators are words in s3 and s7. Two separating points
of the already certified Sylow normal forms suffice to check these words.
The bijective core normal forms then show that homomorphisms are determined
by those two generators. The carrier remains the literal two-core of second.
Source: Parrott (1972), §5, p.683, in the existing Atlas1600 marking.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.SecondCoreAction
open AmalgamRigidity.SecondExtension
namespace CoreGenerators

def generatorIndex : Fin 7 → Fin 1024 := ![1,2,4,16,32,128,256]
def generator (i : Fin 7) : Core := coreNormalForm (generatorIndex i)

theorem generator_val (i : Fin 7) :
    (generator i : second) = gen ⟨i.val+1,by omega⟩ := by
  rw [generator,coreNormalForm_val]
  fin_cases i <;> norm_num [generatorIndex,word] <;> congr 1

def perm : Core →* Equiv.Perm (Fin 1600) :=
  AmalgamRigidity.SecondExtension.perm.comp Core.subtype

theorem perm_generator (i : Fin 7) :
    perm (generator i) = packedGen ⟨i.val+1,by omega⟩ := by
  change AmalgamRigidity.SecondExtension.perm (generator i : second) = _
  rw [generator_val,perm_gen]

private theorem perm_normalForm (n : Fin 1024) :
    perm (coreNormalForm n) = (atlas1600SylowTwoNormalForm ⟨n.val,by omega⟩).val := by
  change (coreNormalForm n).val.val.val = _
  rw [coreNormalForm_val,word_gen_val]

theorem eq_of_points {x y : Core}
    (h0 : perm x 0 = perm y 0) (h930 : perm x 930 = perm y 930) : x = y := by
  obtain ⟨i,rfl⟩ := coreNormalForm_bijective.2 x
  obtain ⟨j,rfl⟩ := coreNormalForm_bijective.2 y
  have he : (⟨i.val,by omega⟩ : Fin 2048) = ⟨j.val,by omega⟩ :=
    atlas1600SylowTwoNormalForm_pair_injective (Prod.ext
      (by simpa only [perm_normalForm] using h0)
      (by simpa only [perm_normalForm] using h930))
  exact congrArg coreNormalForm (Fin.ext (congrArg (fun n : Fin 2048 => n.val) he))

def generatorWord {G : Type*} [Monoid G] (x y : G) : Fin 7 → G :=
  ![x*x*x*y*x*y*x*x*x*y*x*x*x*y,
    y*y*x*x*y*x*x*y,
    x,
    x*y*y*x*x*y*y*x,
    y*x*y*y*y,
    x*x*y*x*y*y*x*y,
    y]

theorem map_generatorWord {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (x y : G) (i : Fin 7) :
    f (generatorWord x y i) = generatorWord (f x) (f y) i := by
  fin_cases i <;> simp [generatorWord]

private theorem words_points : ∀ i : Fin 7,
    generatorWord (packedGen 3) (packedGen 7) i 0 = packedGen ⟨i.val+1,by omega⟩ 0 ∧
    generatorWord (packedGen 3) (packedGen 7) i 930 = packedGen ⟨i.val+1,by omega⟩ 930 := by
  decide +kernel

theorem generatorWord_eq (i : Fin 7) :
    generatorWord (generator 2) (generator 6) i = generator i := by
  apply eq_of_points
  · simpa [map_generatorWord,perm_generator] using (words_points i).1
  · simpa [map_generatorWord,perm_generator] using (words_points i).2

theorem normal_form (n : Fin 1024) :
    coreNormalForm n = generator 0 ^ (n.val % 2) * generator 1 ^ (n.val/2 % 2) *
      generator 2 ^ (n.val/4 % 4) * generator 3 ^ (n.val/16 % 2) *
      generator 4 ^ (n.val/32 % 4) * generator 5 ^ (n.val/128 % 2) *
      generator 6 ^ (n.val/256 % 4) := by
  apply Subtype.ext
  simp only [coreNormalForm_val,Subgroup.coe_mul,Subgroup.coe_pow,generator_val,word]
  rw [Nat.div_eq_of_lt n.isLt]
  simp

/-- Homomorphisms on the literal two-core are determined by s3 and s7. -/
theorem hom_ext {G : Type*} [Monoid G] (f g : Core →* G)
    (h3 : f (generator 2) = g (generator 2))
    (h7 : f (generator 6) = g (generator 6)) : f = g := by
  have hgen (i : Fin 7) : f (generator i) = g (generator i) := by
    rw [← generatorWord_eq i,map_generatorWord,map_generatorWord,h3,h7]
  apply MonoidHom.ext
  intro x
  obtain ⟨n,rfl⟩ := coreNormalForm_bijective.2 x
  rw [normal_form]
  simp only [map_mul,map_pow,hgen]

/-- The actual core automorphism is determined by its two generator images. -/
theorem aut_ext (f g : MulAut Core)
    (h3 : f (generator 2) = g (generator 2))
    (h7 : f (generator 6) = g (generator 6)) : f = g :=
  MulEquiv.toMonoidHom_injective (hom_ext f.toMonoidHom g.toMonoidHom h3 h7)

/-- Automorphism enumeration can retain the two images on the actual carrier. -/
theorem generatorImages_injective : Function.Injective
    (fun f : MulAut Core => (f (generator 2), f (generator 6))) := by
  intro f g h
  exact aut_ext f g (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A word in the two core generators, evaluated at any two proposed images. -/
def normalFormWord {G : Type*} [Monoid G] (x y : G) (n : Fin 1024) : G :=
  generatorWord x y 0 ^ (n.val % 2) * generatorWord x y 1 ^ (n.val/2 % 2) *
    generatorWord x y 2 ^ (n.val/4 % 4) * generatorWord x y 3 ^ (n.val/16 % 2) *
    generatorWord x y 4 ^ (n.val/32 % 4) * generatorWord x y 5 ^ (n.val/128 % 2) *
    generatorWord x y 6 ^ (n.val/256 % 4)

theorem map_normalFormWord {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (x y : G) (n : Fin 1024) :
    f (normalFormWord x y n) = normalFormWord (f x) (f y) n := by
  simp only [normalFormWord,map_mul,map_pow,map_generatorWord]

theorem normalFormWord_eq (n : Fin 1024) :
    normalFormWord (generator 2) (generator 6) n = coreNormalForm n := by
  simp only [normalFormWord,generatorWord_eq]
  exact (normal_form n).symm

/-- Evaluation after any actual automorphism, with its exact original images. -/
theorem normalFormWord_aut (f : MulAut Core) (n : Fin 1024) :
    normalFormWord (f (generator 2)) (f (generator 6)) n = f (coreNormalForm n) := by
  simpa only [MulEquiv.coe_toMonoidHom,normalFormWord_eq] using
    (map_normalFormWord f.toMonoidHom (generator 2) (generator 6) n).symm

end CoreGenerators
end Tits.ExceptionalParabolics.SecondCoreAction
