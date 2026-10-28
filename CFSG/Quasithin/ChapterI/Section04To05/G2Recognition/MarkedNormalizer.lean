module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MarkedCubic

/-!
# The full ambient normalizer of the marked elementary eight

The elementary eight V=F*(M), with its original inclusion into G, is
self-centralizing in G and has full normalizer M. In a Sylow-aligned
conjugate, the overlap with H has index three. Its normalizer inside H
therefore either equals that overlap or is all of H. The latter would
make a factor cubic normalize an elementary eight, contradicting
`MarkedCubic`. Since the marked involution belongs to the eight, the
ambient centralizer lies in H, and hence in the overlap. Self-centralization
inside M now gives ambient self-centralization. The conjugation action
embeds the remaining normalizer quotient in Aut(E8), whose order is 168;
the original M already has the full possible order 1344.

Consequently M is self-normalizing, and every conjugate of V has exactly
the corresponding conjugate of M as normalizer. The statements retain
the literal conjugation maps. These identities turn the marked M of
Aschbacher–Smith (G1)–(G2), printed p.417, into an actual full two-local
subgroup for the recognition argument. `Chapter14MarkedNormalizer` applies
them to SourceLocalData, retaining the aligned eight in Q₁Q₂.

The Sylow-nine and order-27-core exclusions and the final model recognition
remain with `qt-i45-g2-recognition`. In particular these two-local identities
do not replace the exceptional q=3 argument referred to Janko by Fong,
Nagoya Math. J.39 (1970), §6, p.74.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.V_normal V_elementary

omit [Finite G] in
private theorem marked_M_normalizes :
    c.M ≤ normalizer (c.V.map c.M.subtype : Set G) := by
  intro m hm
  apply c.V.le_normalizer_map c.M.subtype
  exact mem_map_of_mem c.M.subtype (show (⟨m,hm⟩ : c.M) ∈ normalizer (c.V : Set c.M) by
    rw [normalizer_eq_top]; trivial)

private theorem aligned_seed_centralizer (z : c.H)
    (hH : c.H = centralizer ({(z:G)} : Set G))
    (E : Subgroup c.H) [IsElementaryAbelian 2 E] (hE : Nat.card E=8)
    (hzE : z ∈ E) (g : G)
    (hmap : E.map c.H.subtype = (c.V.map c.M.subtype).map (MulAut.conj g).toMonoidHom)
    (hI : Nat.card (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom : Subgroup G)=192) :
    centralizer (E.map c.H.subtype : Set G) = E.map c.H.subtype := by
  let a := MulAut.conj g
  let f : c.M →* G := a.toMonoidHom.comp c.M.subtype
  have hf : Function.Injective f := a.injective.comp c.M.subtype_injective
  let X := E.map c.H.subtype
  let M := c.M.map a.toMonoidHom
  have hXM : X = c.V.map f := by
    change E.map c.H.subtype = c.V.map f
    rw [hmap,map_map]
  have hMN : M ≤ normalizer (X : Set G) := by
    change M ≤ normalizer (E.map c.H.subtype : Set G)
    rw [hmap]
    exact (map_mono (marked_M_normalizes c)).trans
      ((c.V.map c.M.subtype).le_normalizer_map a.toMonoidHom)
  let J := M.subgroupOf c.H
  let K := (normalizer (X : Set G)).subgroupOf c.H
  have hJ : Nat.card J=192 := by
    rw [←card_map_of_injective c.H.subtype_injective,subgroupOf_map_subtype,inf_comm]
    exact hI
  have hi : J.index=3 := by
    have hh := J.card_mul_index
    rw [hJ,H_card c] at hh
    omega
  have hK : K=J := by
    rcases (isCoatom_of_index_three J hi).le_iff.mp
      (show J ≤ K from fun _ hm => hMN hm) with he|he
    · obtain ⟨t⟩ := exists_cubic_torus c
      have hn : ((t.x:c.H):G) ∈ normalizer (X : Set G) :=
        (show (t.x:c.H) ∈ K by rw [he]; trivial)
      let : IsElementaryAbelian 2 X := IsElementaryAbelian.map_subtype
      exact (cubic_factor_not_normalizes_eight c t.x t.x_order X
        ((card_map_of_injective c.H.subtype_injective).trans hE) hn).elim
    · exact he
  have hCM : centralizer (X : Set G) ≤ M := by
    intro u hu
    have huH : u ∈ c.H := by
      rw [hH]
      exact mem_centralizer_singleton_iff.mpr
        (hu (z:G) (mem_map_of_mem c.H.subtype hzE)).symm
    have huK : (⟨u,huH⟩ : c.H) ∈ K := centralizer_le_normalizer (X : Set G) hu
    exact (hK ▸ huK : (⟨u,huH⟩ : c.H) ∈ J)
  apply le_antisymm ?_ X.le_centralizer
  intro u hu
  obtain ⟨m,hm,he⟩ := hCM hu
  have hmV : (⟨m,hm⟩ : c.M) ∈ c.V := by
    rw [←V_centralizer c]
    intro v hv
    apply hf
    simp only [map_mul]
    have hmval : f ⟨m,hm⟩=u := he
    rw [hmval]
    exact hu (f v) (hXM.symm ▸ mem_map_of_mem f hv)
  rw [hXM]
  exact ⟨⟨m,hm⟩,hmV,he⟩

/-- The original marked eight is self-centralizing in the whole group. -/
theorem V_ambient_centralizer :
    centralizer (c.V.map c.M.subtype : Set G) = c.V.map c.M.subtype := by
  obtain ⟨z,hz,hline,hH⟩ := exists_marked_involution c
  let T : Sylow 2 c.H := default
  have hzQ : z ∈ quaternionCore c := by
    have hh : z ∈ c.H₁ ⊓ c.H₂ := hline ▸ mem_zpowers z
    rw [←quaternionCore_center c] at hh
    exact map_subtype_le _ hh
  obtain ⟨E,he,hE,_,hzE,⟨g,hmap,_,hI⟩,_⟩ := exists_seed_in_H_sylow c T z hz
    (quaternionCore_le_sylow c T hzQ) hH
  let := he
  have hC := aligned_seed_centralizer c z hH E hE hzE g hmap hI
  let A := c.V.map c.M.subtype
  let a := MulAut.conj g
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map_subtype
  apply le_antisymm ?_ A.le_centralizer
  intro u hu
  have huc : a u ∈ centralizer (E.map c.H.subtype : Set G) := by
    rw [hmap]
    rintro v ⟨w,hw,rfl⟩
    exact (map_mul a w u).symm.trans ((congrArg a (hu w hw)).trans (map_mul a u w))
  rw [hC,hmap] at huc
  exact (mem_map_iff_mem a.injective).mp huc

/-- The original M is the full ambient normalizer of its marked eight. -/
theorem M_seed_normalizer : normalizer (c.V.map c.M.subtype : Set G) = c.M := by
  let A := c.V.map c.M.subtype
  let N := normalizer (A : Set G)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map_subtype
  have hA : Nat.card A=8 := (card_map_of_injective c.M.subtype_injective).trans (V_card c)
  have hk : Nat.card A.normalizerMonoidHom.ker=8 := by
    rw [normalizerMonoidHom_ker,V_ambient_centralizer c,
      Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv]
    exact hA
  have hr : Nat.card A.normalizerMonoidHom.range ≤ 168 := by
    exact A.normalizerMonoidHom.range.card_le_card_group.trans_eq
      (card_mulAut_of_elementary_eight A hA)
  have hN : Nat.card N ≤ 1344 := by
    have hh := A.normalizerMonoidHom.ker.card_mul_index
    rw [hk,index_ker] at hh
    change 8 * Nat.card A.normalizerMonoidHom.range = Nat.card N at hh
    omega
  exact (eq_of_le_of_card_ge (marked_M_normalizes c)
    (hN.trans_eq (M_card c).symm)).symm


/-- The marked local subgroup is self-normalizing in the ambient group. -/
theorem M_self_normalizing : normalizer (c.M : Set G) = c.M := by
  apply le_antisymm ?_ c.M.le_normalizer
  have hh := normalizer_le_normalizer_characteristic_image c.M (pCore 2 c.M)
  rw [←V_eq_pCore c,M_seed_normalizer c] at hh
  exact hh

/-- Every literal conjugate of the marked eight has the corresponding
conjugate of M as its full ambient normalizer. -/
theorem conjugate_seed_normalizer (g : G) :
    normalizer ((c.V.map c.M.subtype).map (MulAut.conj g).toMonoidHom : Set G) =
      c.M.map (MulAut.conj g).toMonoidHom := by
  rw [←map_equiv_normalizer_eq,M_seed_normalizer c]

/-- A conjugator stabilizes the marked eight exactly when it belongs to M. -/
theorem seed_conjugate_eq_iff (g : G) :
    (c.V.map c.M.subtype).map (MulAut.conj g).toMonoidHom = c.V.map c.M.subtype ↔
      g ∈ c.M := by
  constructor
  · intro h
    rw [←M_seed_normalizer c]
    exact mem_normalizer_iff_map_conj_eq.mpr h
  · intro h
    apply mem_normalizer_iff_map_conj_eq.mp
    rwa [M_seed_normalizer c]


/-- Ambient self-centralization is retained by every marked conjugate. -/
theorem conjugate_seed_centralizer (g : G) :
    centralizer ((c.V.map c.M.subtype).map (MulAut.conj g).toMonoidHom : Set G) =
      (c.V.map c.M.subtype).map (MulAut.conj g).toMonoidHom := by
  let A := c.V.map c.M.subtype
  let a := MulAut.conj g
  let B := A.map a.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map a.toMonoidHom
  apply le_antisymm ?_ B.le_centralizer
  intro u hu
  have hi : a.symm u ∈ centralizer (A : Set G) := by
    intro v hv
    apply a.injective
    simp only [map_mul,a.apply_symm_apply]
    exact hu (a v) (mem_map_of_mem a.toMonoidHom hv)
  rw [V_ambient_centralizer c] at hi
  exact ⟨a.symm u,hi,a.apply_symm_apply u⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
