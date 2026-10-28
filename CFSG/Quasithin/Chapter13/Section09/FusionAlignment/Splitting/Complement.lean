module
public import Theory.SpecificGroups.SymmetricFourWreath.Complement
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.NormalizerOrbit
/-!
# Splitting the actual normalizer of the marked binary module

The native wreath complement transports into the original Sylow two-subgroup.
Gaschütz's theorem then produces a complement to B inside the literal N_G(B).
No extension splitting, abstract normalizer model or complement is assumed.
This supplies the source extension step in Aschbacher–Smith 13.9.10.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

private theorem complement_map {H L : Subgroup P}
    (hc : H.IsComplement' L) {J:Type*} [Group J] (f:P→*J)
    (hf : Function.Bijective f) : (H.map f).IsComplement' (L.map f) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply disjoint_def.mpr
    rintro x ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
    have he' : b=a := hf.1 he
    subst b
    rw [disjoint_def.mp hc.disjoint ha hb,map_one]
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨y,rfl⟩ := hf.2 x
    obtain ⟨⟨a,b⟩,he⟩ := hc.2 y
    exact ⟨f a,mem_map_of_mem _ a.property,f b,mem_map_of_mem _ b.property,
      (map_mul f _ _).symm.trans (congrArg f he)⟩

/-- Gaschütz supplies a complement in the original N_G(B). -/
theorem exists_normalizer_complement :
    ∃L:Subgroup (normalizer (m.B:Set G)),
      (m.B.subgroupOf (normalizer (m.B:Set G))).IsComplement' L := by
  let K := normalizer (m.B:Set G)
  let V := m.B.subgroupOf K
  let S : Sylow 2 K := d.T.subtype m.sylow_le_normalizer_B
  let f₀ := m.embedding.comp sylowEmbedding
  have hr : f₀.range = (d.T:Subgroup G) := by
    rw [MonoidHom.range_comp]
    exact m.image_standardSylow
  let f : P→*S :=
    { toFun x := ⟨⟨f₀ x,m.sylow_le_normalizer_B (hr ▸ (show f₀ x∈f₀.range from ⟨x,rfl⟩))⟩,
        (by change f₀ x∈(d.T:Subgroup G); rw [←hr]; exact ⟨x,rfl⟩)⟩
      map_one' := Subtype.ext (Subtype.ext (map_one f₀))
      map_mul' x y := Subtype.ext (Subtype.ext (map_mul f₀ x y)) }
  have hfinj : Function.Injective f := by
    intro a b h
    exact (m.embedding_injective.comp sylowEmbedding_injective) (congrArg (fun x:S => (x:G)) h)
  have hfsurj : Function.Surjective f := by
    intro x
    obtain ⟨a,ha⟩ := (hr ▸ x.property : (x:G)∈f₀.range)
    exact ⟨a,Subtype.ext (Subtype.ext ha)⟩
  have he : (elementaryInP false false).map f = V.subgroupOf (S:Subgroup K) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact mem_map_of_mem m.embedding (mem_map_of_mem sylowEmbedding ha)
    · intro hx
      obtain ⟨b,⟨a,ha,rfl⟩,he⟩ := hx
      exact ⟨a,ha,Subtype.ext (Subtype.ext he)⟩
  have hc := complement_map elementaryInP_complement f ⟨hfinj,hfsurj⟩
  rw [he] at hc
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf m.B.le_normalizer
  exact (Subgroup.exists_complement_iff_sylow V (IsElementaryAbelian.isPGroup 2 V) S).mpr
    ⟨planeComplement.map f,hc⟩

end CFSG.Quasithin.Chapter13.Section09.Marking
