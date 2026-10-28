module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms.Generators

/-!
Every automorphism of the native J₂ Borel is realized by conjugation in its
concrete outer extension.  The proof normalizes an automorphism on the order
8 generator, applies the checked orbit table to the second generator, then
uses pair generation.  This formalizes the Borel extension input used in the
DGS quasithin branch (DGS, §10.9, pp. 162–163).
-/

public section
open Subgroup
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms
open Theory.GroupTheory GeneratorPair Seed PairNormalizer
open PairNormalizer.SylowData PairNormalizer.QuotientData
open GeneratorPair.SecondOrbitCertificate Overlap

def embedding : B →* Extension := intoExtension.comp B.subtype

private def permEmbedding : B →* Equiv.Perm (Fin 100) := inclusion.comp B.subtype

private theorem permEmbedding_injective : Function.Injective permEmbedding :=
  inclusion_injective.comp B.subtype_injective

private theorem permEmbedding_bElement (i : Fin 384) :
    permEmbedding (bElement i) = bTable i := bElement_table i

private theorem permEmbedding_x : permEmbedding x = xTable := x_table
private theorem permEmbedding_v : permEmbedding v = oddTable 1 := v_table

def extensionElement (i : Fin 768) : outerB :=
  ⟨intoExtension (bElement ⟨i.val % 384,Nat.mod_lt _ (by decide)⟩ : Carrier) *
    outerElement ^ (i.val / 384),
    outerB.mul_mem
      ((show B.map intoExtension ≤ outerB from le_sup_left)
        (mem_map_of_mem _ (bElement _).property))
      ((show zpowers outerElement ≤ outerB from le_sup_right)
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))⟩

theorem extensionElement_table (i : Fin 768) :
    extension.subtype (extensionElement i : Extension) = extensionTable i := by
  change extension.subtype (intoExtension (bElement _ : Carrier) * outerElement ^ _) = _
  rw [map_mul,map_pow,outerElement_inclusion]
  change inclusion (bElement _ : Carrier) * _ = _
  rw [bElement_table]
  rfl

theorem x_pow8 : x ^ 8 = 1 := by
  apply Subtype.ext
  apply inclusion_injective
  change inclusion ((x : Carrier) ^ 8) = inclusion 1
  rw [map_pow,map_one,x_table]
  exact x_relations.1

theorem x_pow4_ne : x ^ 4 ≠ 1 := by
  intro h
  apply x_relations.2.1
  have he := congrArg (fun b : B => inclusion (b : Carrier)) h
  change inclusion ((x : Carrier) ^ 4) = inclusion 1 at he
  simpa only [map_pow,map_one,x_table] using he

theorem xv_pow6_ne : (x * v) ^ 6 ≠ 1 := by
  intro h
  apply x_relations.2.2.1
  have he := congrArg (fun b : B => inclusion (b : Carrier)) h
  change inclusion (((x : Carrier) * (v : Carrier)) ^ 6) = inclusion 1 at he
  simpa only [map_pow,map_mul,map_one,x_table,v_table] using he

theorem xvinv_pow6 : (x * v⁻¹) ^ 6 = 1 := by
  apply Subtype.ext
  apply inclusion_injective
  change inclusion (((x : Carrier) * (v : Carrier)⁻¹) ^ 6) = inclusion 1
  rw [map_pow,map_mul,map_inv,map_one,x_table,v_table]
  exact x_relations.2.2.2

set_option maxHeartbeats 400000 in
theorem first_generator_conjugate (d : MulAut B) :
    ∃ c : B, c * x * c⁻¹ = d x := by
  obtain ⟨i,hi⟩ := exists_bElement (d x)
  have h8 : bTable i ^ 8 = 1 := by
    have h : (bElement i) ^ 8 = 1 := by rw [hi,←map_pow,x_pow8,map_one]
    have he := congrArg permEmbedding h
    rwa [map_pow,map_one,permEmbedding_bElement] at he
  have h4 : bTable i ^ 4 ≠ 1 := by
    intro h
    have hb : (bElement i)^4 = 1 := by
      apply permEmbedding_injective
      rw [map_pow,map_one,permEmbedding_bElement]
      exact h
    rw [hi,←map_pow] at hb
    exact x_pow4_ne (d.injective (hb.trans (map_one d).symm))
  refine ⟨bElement (xConjIndex i), ?_⟩
  rw [←hi]
  apply permEmbedding_injective
  rw [map_mul,map_mul,map_inv,permEmbedding_bElement,permEmbedding_bElement,
    permEmbedding_x]
  exact x_orbit_check i h8 h4

set_option maxHeartbeats 400000 in
theorem normalized_pair_conjugate (d : MulAut B) (hx : d x = x) :
    ∃ g : outerB,
      (g : Extension) * embedding x * (g : Extension)⁻¹ = embedding (d x) ∧
      (g : Extension) * embedding v * (g : Extension)⁻¹ = embedding (d v) := by
  obtain ⟨i,hi⟩ := exists_bElement (d v)
  have hv3 : v ^ 3 = 1 := by
    apply Subtype.ext
    exact orderOf_dvd_iff_pow_eq_one.mp (v_order ▸ dvd_rfl)
  have hvne : v ≠ 1 := by
    intro h
    have he : (v : Carrier) = 1 := congrArg Subtype.val h
    change oddGenerator 1 = 1 at he
    have ho := v_order
    rw [he,orderOf_one] at ho
    omega
  have h3 : bTable i ^ 3 = 1 := by
    have h : bElement i ^ 3 = 1 := by rw [hi,←map_pow,hv3,map_one]
    have he := congrArg permEmbedding h
    rwa [map_pow,map_one,permEmbedding_bElement] at he
  have hne : bTable i ≠ 1 := by
    intro h
    have hb : bElement i = 1 := by
      apply permEmbedding_injective
      rw [permEmbedding_bElement,map_one]
      exact h
    rw [hi] at hb
    exact hvne (d.injective (hb.trans (map_one d).symm))
  have h6ne : (xTable * bTable i) ^ 6 ≠ 1 := by
    intro h
    have hb : (x * bElement i)^6 = 1 := by
      apply permEmbedding_injective
      rw [map_pow,map_mul,map_one,permEmbedding_bElement,permEmbedding_x]
      exact h
    rw [hi,←hx,←map_mul,←map_pow] at hb
    exact xv_pow6_ne (d.injective (hb.trans (map_one d).symm))
  have h6 : (xTable * (bTable i)⁻¹) ^ 6 = 1 := by
    have hb : (x * (bElement i)⁻¹)^6 = 1 := by
      rw [hi,←hx,←map_inv,←map_mul,←map_pow,xvinv_pow6,map_one]
    have he := congrArg permEmbedding hb
    rwa [map_pow,map_mul,map_inv,map_one,permEmbedding_bElement,permEmbedding_x] at he
  obtain ⟨hx',hv'⟩ := v_orbit_check i h3 hne h6ne h6
  refine ⟨extensionElement (vConjIndex i),?_,?_⟩
  · rw [hx]
    apply extension.subtype_injective
    rw [map_mul,map_mul,map_inv,extensionElement_table]
    change _ * inclusion (x : Carrier) * _ = inclusion (x : Carrier)
    simpa only [x_table] using hx'
  · rw [←hi]
    apply extension.subtype_injective
    rw [map_mul,map_mul,map_inv,extensionElement_table]
    change _ * inclusion (v : Carrier) * _ = inclusion (bElement i : Carrier)
    simpa only [v_table,bElement_table] using hv'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem automorphism_coverage (d : MulAut B) : ∃ g : outerB, ∀ b : B,
    intoExtension (d b : Carrier) =
      (g : Extension) * intoExtension (b : Carrier) * (g : Extension)⁻¹ := by
  obtain ⟨c,hc⟩ := first_generator_conjugate d
  let d' := d.trans (MulAut.conj c⁻¹)
  have hd'x : d' x = x := by
    change c⁻¹ * d x * (c⁻¹)⁻¹ = x
    rw [←hc]
    group
  obtain ⟨g,hgx,hgv⟩ := normalized_pair_conjugate d' hd'x
  have he : embedding.comp d'.toMonoidHom =
      (MulAut.conj (g : Extension)).toMonoidHom.comp embedding :=
    hom_ext _ _ hgx.symm hgv.symm
  let cg : outerB :=
    ⟨intoExtension (c : Carrier), (show B.map intoExtension ≤ outerB from le_sup_left)
      (mem_map_of_mem _ c.property)⟩
  refine ⟨cg * g,fun b => ?_⟩
  have hb := DFunLike.congr_fun he b
  change embedding (d' b) = (g : Extension) * embedding b * (g : Extension)⁻¹ at hb
  have hd : d b = c * d' b * c⁻¹ := by
    change d b = c * (c⁻¹ * d b * (c⁻¹)⁻¹) * c⁻¹
    group
  change embedding (d b) = (embedding c * (g : Extension)) *
    embedding b * (embedding c * (g : Extension))⁻¹
  rw [hd,map_mul,map_mul,map_inv,hb]
  group

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms
