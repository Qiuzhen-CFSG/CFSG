module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Labels.Unique

/-!
# Existence of the original color label of a normalized five

In the z-centralizer, the image of an original five is a Sylow five of S5.
Normalization by the marked four-group makes that pentagon fixed by u*,
so the canonical original parabolic contains both the five and the pair.
Actual source pair symmetries transport this argument to each color.
Source: the parabolic incidence argument of J.4.10, printed p.444.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (p : Plane d) (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
  (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹)
  (c : Choices d) (e : first ≃* p.F₁ B5) (hz : (e modelZ : G)=c.z)
  (hfive : (zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
include s hi hz hfive

/-- A normalized original five in C_G(z) determines a member of the z family. -/
theorem exists_z_member_of_five (B : Subgroup G) (hB : Nat.card B=5)
    (hBc : B≤centralizer ({c.z} : Set G))
    (hBN : pairSpan c.z (sourceU e)≤normalizer (B : Set G)) :
    ∃ E ∈ colorFamily p B5 c.z (sourceU e) c.z, B≤E := by
  have hBH : B≤d.toTypeRuSetup.H := c.H_eq_centralizer_z.symm ▸ hBc
  let J := (B.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap
  have hJ : Nat.card J=5 := five_quotient_image_card B hBH hB
  have hp : IsPGroup 5 J := IsPGroup.of_card (n:=1) (by simpa using hJ)
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hJP : J=(P : Subgroup S5) := eq_of_le_of_card_ge hP (by
    rw [hJ,Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.card_sylow P])
  have huN := hBN (mem_sup_right (mem_zpowers (sourceU e)))
  have him : d.ru2.quotientMap (sourceInverter p B5 e) ∈ normalizer ((P : Subgroup S5) : Set S5) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro x ⟨a,ha,rfl⟩
      rw [←hJP] at ha ⊢
      obtain ⟨b,hb,rfl⟩ := ha
      have hconj : sourceInverter p B5 e*b*(sourceInverter p B5 e)⁻¹ ∈ B.subgroupOf d.toTypeRuSetup.H :=
        (mem_normalizer_iff.mp huN (b : G)).mp hb
      have hm := mem_map_of_mem d.ru2.quotientMap hconj
      change d.ru2.quotientMap (sourceInverter p B5 e) * d.ru2.quotientMap b *
        (d.ru2.quotientMap (sourceInverter p B5 e))⁻¹ ∈ J
      simpa only [map_mul,map_inv] using hm
    · rw [card_map_of_injective (MulAut.conj _).injective]
  refine ⟨parabolicFor p B5 P,?_,five_le_parabolicFor_of_image p s B5 hi P B hBH hB hP⟩
  rw [colorFamily_z p B5 c e hz]
  exact ⟨parabolicFor_mem p B5 P,(source_family_mem_iff p s B5 hi c e hz hfive P).mpr him⟩

omit s hi hz hfive in
private theorem normalizes_span (z u n : G)
    (hz : n*z*n⁻¹ ∈ pairSpan z u) (hu : n*u*n⁻¹ ∈ pairSpan z u) :
    n ∈ normalizer (pairSpan z u : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [pairSpan,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    exact sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hu)
  · rw [card_map_of_injective (MulAut.conj n).injective]

variable {D : Type*} [Group D] (q : Completion D) (f : D →* G)
  (hleft : ∀ a : first,f (q.left a)=(e a : G))
include q f hleft

omit s hi in
/-- The genuine source symmetries carry any of the three colors back to z. -/
theorem source_color_transporter (v : G) (hv : v ∈ colors c.z (sourceU e)) :
    ∃ n : G, n ∈ normalizer (pairSpan c.z (sourceU e) : Set G) ∧ n*v*n⁻¹=c.z := by
  obtain ⟨a,_,haz,hau⟩ := source_mark_swap q c B5 e f hleft hz hfive
  have haN : a ∈ normalizer (pairSpan c.z (sourceU e) : Set G) :=
    normalizes_span c.z (sourceU e) a
      (by rw [haz]; exact mem_sup_right (mem_zpowers (sourceU e)))
      (by rw [hau]; exact mem_sup_left (mem_zpowers c.z))
  obtain ⟨r,_,_,_,hrz,hru,_,_,_,_⟩ := source_two_transvections q c B5 e f hleft hz hfive
  have hrN : r ∈ normalizer (pairSpan c.z (sourceU e) : Set G) :=
    normalizes_span c.z (sourceU e) r
      (by rw [hrz]; exact mem_sup_left (mem_zpowers c.z))
      (by rw [hru]; exact mul_mem_sup (mem_zpowers c.z) (mem_zpowers (sourceU e)))
  simp only [colors,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  · exact ⟨1,one_mem _,by simp⟩
  · exact ⟨a,haN,hau⟩
  · refine ⟨a*r⁻¹,mul_mem haN (inv_mem hrN),?_⟩
    calc
      _ = a*(r⁻¹*(c.z*sourceU e)*r)*a⁻¹ := by group
      _ = a*sourceU e*a⁻¹ := by rw [←hru]; congr 1; group
      _ = c.z := hau

/-- Any literal five centralized by its color and normalized by the pair
belongs to an original member of that color family. -/
theorem exists_color_member_of_five (v : G) (hv : v ∈ colors c.z (sourceU e))
    (B : Subgroup G) (hB : Nat.card B=5) (hBc : B≤centralizer ({v} : Set G))
    (hBN : pairSpan c.z (sourceU e)≤normalizer (B : Set G)) :
    ∃ E ∈ colorFamily p B5 c.z (sourceU e) v, B≤E := by
  obtain ⟨n,hn,hnv⟩ := source_color_transporter p B5 c e hz hfive q f hleft v hv
  let A := B.conjBy n
  have hA : Nat.card A=5 := (card_map_of_injective (MulAut.conj n).injective).trans hB
  have hAc : A≤centralizer ({c.z} : Set G) := by
    rintro x ⟨b,hb,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj n) (mem_centralizer_singleton_iff.mp (hBc hb))
    change (n*b*n⁻¹)*c.z=c.z*(n*b*n⁻¹)
    simpa only [map_mul,MulAut.conj_apply,hnv] using hh
  have hnV : (pairSpan c.z (sourceU e)).map (MulAut.conj n).toMonoidHom=pairSpan c.z (sourceU e) :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have hAN : pairSpan c.z (sourceU e)≤normalizer (A : Set G) := by
    have hh := map_mono (f := (MulAut.conj n).toMonoidHom) hBN
    rw [hnV,map_equiv_normalizer_eq] at hh
    exact hh
  obtain ⟨E,hE,hAE⟩ := exists_z_member_of_five p s B5 hi c e hz hfive A hA hAc hAN
  refine ⟨E.conjBy n⁻¹,?_,?_⟩
  · have hh := color_conjugate_mem p B5 c.z (sourceU e) n⁻¹ (inv_mem hn) hE
    have hback : n⁻¹*c.z*(n⁻¹)⁻¹=v := by rw [←hnv]; group
    rwa [hback] at hh
  · have hh := map_mono (f := (MulAut.conj n⁻¹).toMonoidHom) hAE
    change (B.conjBy n).conjBy n⁻¹≤E.conjBy n⁻¹ at hh
    rwa [conjBy_inv] at hh

/-- The actual source color and five subgroup determine exactly one original parabolic. -/
theorem source_unique_five_label (v : G) (hv : v ∈ colors c.z (sourceU e))
    (B : Subgroup G) (hB : Nat.card B=5) (hBc : B≤centralizer ({v} : Set G))
    (hBN : pairSpan c.z (sourceU e)≤normalizer (B : Set G)) :
    ∃! E : Subgroup G, E ∈ colorFamily p B5 c.z (sourceU e) v ∧ B≤E :=
  existsUnique_color_member p s B5 hi c e hB
    (exists_color_member_of_five p s B5 hi c e hz hfive q f hleft v hv B hB hBc hBN)

/-- The canonical original parabolic determined by an admissible color-five pair. -/
@[expose] def sourceFiveLabel (v : G) (hv : v ∈ colors c.z (sourceU e))
    (B : Subgroup G) (hB : Nat.card B=5) (hBc : B≤centralizer ({v} : Set G))
    (hBN : pairSpan c.z (sourceU e)≤normalizer (B : Set G)) : Subgroup G :=
  fiveLabel p B5 c e v B
    (exists_color_member_of_five p s B5 hi c e hz hfive q f hleft v hv B hB hBc hBN)

/-- Both defining properties concern the original literal five and subgroup. -/
theorem sourceFiveLabel_spec (v : G) (hv : v ∈ colors c.z (sourceU e))
    (B : Subgroup G) (hB : Nat.card B=5) (hBc : B≤centralizer ({v} : Set G))
    (hBN : pairSpan c.z (sourceU e)≤normalizer (B : Set G)) :
    sourceFiveLabel p s B5 hi c e hz hfive q f hleft v hv B hB hBc hBN ∈
      colorFamily p B5 c.z (sourceU e) v ∧
    B≤sourceFiveLabel p s B5 hi c e hz hfive q f hleft v hv B hB hBc hBN :=
  fiveLabel_spec p B5 c e v B _

/-- The canonical label equals every actual member containing the same five. -/
theorem sourceFiveLabel_eq (v : G) (hv : v ∈ colors c.z (sourceU e))
    (B : Subgroup G) (hB : Nat.card B=5) (hBc : B≤centralizer ({v} : Set G))
    (hBN : pairSpan c.z (sourceU e)≤normalizer (B : Set G))
    (E : Subgroup G) (hE : E ∈ colorFamily p B5 c.z (sourceU e) v) (hBE : B≤E) :
    sourceFiveLabel p s B5 hi c e hz hfive q f hleft v hv B hB hBc hBN=E :=
  fiveLabel_eq p s B5 hi c e v B hB _ E hE hBE

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
