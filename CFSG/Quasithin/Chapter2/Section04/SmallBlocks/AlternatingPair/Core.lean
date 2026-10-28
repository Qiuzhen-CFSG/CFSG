module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Normalizer
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer

/-! The original A₅ module is disjoint from O₂(G_I). If it lay in that
normal core, its escaping conjugate would lie in O₂(L Baum(S)), which
centralizes the original module. Irreducibility reduces intersection to
this impossible containment. Source 2.4.25, printed p.542. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem alternating_module_disjoint_of_not_le
    (K N : Subgroup G) (hK : IsAlternatingBlock K 5)
    (hKN : K ≤ normalizer (N : Set G)) (hnot : ¬ sourceModule K ≤ N) :
    Disjoint (sourceModule K) N := by
  let U := sourceModule K
  let W := U ⊓ N
  have hUK : U ≤ K := map_subtype_le _
  have hKW : K ≤ normalizer (W : Set G) :=
    (le_inf (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (blockU K)))
      hKN).trans inf_normalizer_le_normalizer_inf
  have hWK : W ≤ K := inf_le_left.trans hUK
  let : (W.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hKW
  have hz : blockU K ⊓ center K = ⊥ := by
    rw [←blockFixed_map,hK.blockFixed_eq_bot,Subgroup.map_bot]
  have hWU : W.subgroupOf K ≤ blockU K := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hx.1
    exact (Subtype.ext he : y=x) ▸ hy
  rcases hK.2.1.irreducible.2 (W.subgroupOf K) inferInstance (hz ▸ bot_le) hWU with he | he
  · have hm := congrArg (map K.subtype) he
    rw [map_subgroupOf_eq_of_le hWK,hz,Subgroup.map_bot] at hm
    exact disjoint_iff.mpr hm
  · apply False.elim
    apply hnot
    have hm := congrArg (map K.subtype) he
    rw [map_subgroupOf_eq_of_le hWK] at hm
    exact hm.ge.trans inf_le_right

variable {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.module_disjoint_phi_core
    (c : AlternatingPairSourceSetup d M₀) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    Disjoint (sourceModule L) (twoCore (normalizer (Phi S L : Set G))) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let GI := normalizer (Phi S L : Set G)
  let Q := twoCore GI
  let B := ChapterB.baumann S
  let Y := L ⊔ B
  let U := sourceModule L
  have hLG : L ≤ GI := (le_centralizer_iff.mp (Phi_le_centralizer S L)).trans
    (Subgroup.centralizer_le_normalizer _)
  have hBG : B ≤ GI := (le_inf inf_le_left c.marked₁.normalizes).trans
    ((normalizer_Phi_eq c.marked₁ c.marked₂).ge.trans inf_le_right)
  have hYG : Y ≤ GI := sup_le hLG hBG
  have hxS := c.original.R_normal c.x_mem
  have hxG : c.x ∈ GI := conjugator_normalizes_Phi c.marked₁ c.marked₂ c.x hxS c.noncommuting
  apply alternating_module_disjoint_of_not_le L Q c.marked₁.block
    (hLG.trans (le_normalizer_twoCore GI))
  intro hUQ
  let V := U.map (MulAut.conj c.x⁻¹).toMonoidHom
  have hVQ : V ≤ Q := by
    have hxQ := (le_normalizer_twoCore GI) (GI.inv_mem hxG)
    have hm := map_mono (f := (MulAut.conj c.x⁻¹).toMonoidHom) hUQ
    have he : Q.map (MulAut.conj c.x⁻¹).toMonoidHom = Q :=
      mem_normalizer_iff_map_conj_eq.mp hxQ
    exact hm.trans_eq he
  have hVB : V ≤ B := by
    have hxB := Stellmacher.normalizer_le_normalizer_baumann S ((normalizer (S:Set G)).inv_mem hxS)
    have hm := map_mono (f := (MulAut.conj c.x⁻¹).toMonoidHom) c.marked₁.module_le
    have he : B.map (MulAut.conj c.x⁻¹).toMonoidHom = B :=
      mem_normalizer_iff_map_conj_eq.mp hxB
    exact hm.trans_eq he
  have hN : Y ≤ normalizer (Q ⊓ Y : Set G) :=
    (le_inf (hYG.trans (le_normalizer_twoCore GI)) Y.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hcore : Q ⊓ Y ≤ Y.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 GI).to_le inf_le_left) inf_le_right hN
  have hVC : V ≤ centralizer (U : Set G) := by
    have hh := (le_inf hVQ (hVB.trans le_sup_right)).trans hcore
    rw [c.marked₁.core] at hh
    exact hh.trans inf_le_right
  exact c.noncommuting hVC
end CFSG.Quasithin.Chapter2
