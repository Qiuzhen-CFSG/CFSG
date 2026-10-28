module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ThompsonPairNormalizers
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingCoreSource
public import Theory.GroupTheory.PlaneNormalizerChoice
/-! # The source normalizer contradiction and square rechoice
For the selected component plane, the source index and centralizer geometry
produce the beta normalizer. An invariant crossing yields a characteristic-two
normalizer with a large beta base, contradicting empty gammaEvenZero.
The remaining case admits an outside actor whose square moves the plane.
Model plane geometry stays explicit here and is discharged by the model assembly.
Source: Aschbacher--Smith 2.5.7, printed p.556.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.plane_normalizer_mem_beta
    (c:MathieuSourceSetup H L M S z) {κ:GroupClass} (hG:IsSimpleQTKE κ G)
    (V:Subgroup G) (hV:V≤(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)≤normalizer (V:Set G))
    (hcore:twoCore H≤normalizer (V:Set G))
    (hi:((S:Subgroup H).map H.subtype⊓normalizer (V:Set G)).relIndex ((S:Subgroup H).map H.subtype)≤2) :
    ((S:Subgroup H).map H.subtype⊓normalizer (V:Set G))∈beta M := by
  let Y:=(S:Subgroup H).map H.subtype
  let N:=Y⊓normalizer (V:Set G)
  have hVN:V≤N:=le_inf hV V.le_normalizer
  have hJN:elementaryAbelianMaxJ Y≤N:=le_inf (sSup_le fun _ h=>h.1) hJ
  have hCN:twoCore H≤N:=le_inf (pCoreIn_le_sylow H S) hcore
  have hCR:Y⊓centralizer (N:Set G)≤N:=
    le_inf inf_le_left (inf_le_right.trans ((centralizer_le hVN).trans (Subgroup.centralizer_le_normalizer _)))
  change N.relIndex Y≤2 at hi
  change N∈beta M
  have hn:N.relIndex Y≠0:=index_ne_zero_of_finite
  have hcases:N.relIndex Y=1∨N.relIndex Y=2:=by omega
  rcases hcases with h1|h2
  · have he:N=Y:=le_antisymm inf_le_left (relIndex_eq_one.mp h1)
    rw [he]
    exact beta_mono c.pair.1.1 c.base_le (S.isPGroup'.map H.subtype)
  · exact lemma_2_3_9_8 hG c.T c.maximal c.sylow_le c.unique c.gamma c.pair S c.base_le
      hJN hCN inf_le_left h2 hCR

theorem MathieuSourceSetup.invariant_crossing_plane_false
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    {κ:GroupClass} (hG:IsSimpleQTKE κ G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (V X:Subgroup G)
    (hVR:V≤elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))
    (hRV:elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)≤normalizer (V:Set G))
    (hcore:twoCore H≤normalizer (V:Set G))
    (hi:((S:Subgroup H).map H.subtype⊓normalizer (V:Set G)).relIndex ((S:Subgroup H).map H.subtype)≤2)
    (hcent:elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓centralizer (V:Set G)≤V⊔twoCore H)
    (hVX:V≤X) (hXL:X≤L) (hXV:X≤normalizer (V:Set G)) (hout:¬X≤M)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxR:x∈normalizer (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype):Set G))
    (hxN:x∈normalizer (((S:Subgroup H).map H.subtype⊓normalizer (V:Set G)):Set G))
    (hx2:x^2∈normalizer (V:Set G))
    (hcross:V.conjBy x≤centralizer (V:Set G)) : False := by
  let Y:=(S:Subgroup H).map H.subtype
  let R:=elementaryAbelianMaxJ Y
  let N:=Y⊓normalizer (V:Set G)
  let Z:=zpowers z
  let I:=Z⊔(V⊔V.conjBy x)
  let U:=N⊔zpowers x
  have hRY:R≤Y:=sSup_le fun _ h=>h.1
  have hVY:V≤Y:=hVR.trans hRY
  have hzcomm (a:G) (ha:a∈c.T):a*z=z*a:=by
    obtain ⟨w,hw,he⟩:=c.mem_center
    have hh:=congrArg Subtype.val (mem_center_iff.mp hw ⟨a,ha⟩)
    change a*(w:G)=(w:G)*a at hh
    change (w:G)=z at he
    rwa [he] at hh
  have hTZ:(c.T:Subgroup G)≤normalizer (Z:Set G):=by
    apply (show (c.T:Subgroup G)≤centralizer (Z:Set G) from ?_).trans (Subgroup.centralizer_le_normalizer _)
    apply le_centralizer_iff.mp
    apply zpowers_le.mpr
    exact hzcomm
  have hzY:z∈Y:=c.center_le c.mem_center
  have hzR:z∈R:=by
    obtain ⟨B,hB⟩:=elementaryAbelianMaxSubgroups_nonempty Y
    exact (le_sSup hB) (mem_maxFamily_of_central_involution hB hzY
      (by simpa only [c.involution] using pow_orderOf_eq_one z)
      (fun b hb=>hzcomm b (c.sylow_lt.le (hB.1 hb))))
  have hVxR:V.conjBy x≤R:=by
    rintro _ ⟨a,ha,rfl⟩
    exact (hxR a).mp (hVR ha)
  have hIY:I≤Y:=sup_le (zpowers_le.mpr hzY) (sup_le hVY (hVxR.trans hRY))
  have hIC:I≤V⊔twoCore H:=by
    apply sup_le
    · apply zpowers_le.mpr
      exact hcent ⟨hzR,fun v hv=>hzcomm v (c.sylow_lt.le (hVY hv))⟩
    · exact sup_le le_sup_left ((le_inf hVxR hcross).trans hcent)
  have hVI:V≤I:=le_sup_left.trans le_sup_right
  have hcoreC:twoCore H≤centralizer (X:Set G):=by
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact inf_le_right.trans (centralizer_le hXL)
  have hXI:X≤normalizer (I:Set G):=
    normalizes_intermediate_of_centralizing_factor X V (twoCore H) I hVX hXV hcoreC hVI hIC
  have hNV:N≤normalizer (V:Set G):=inf_le_right
  have hNVx:N≤normalizer (V.conjBy x:Set G):=by
    rw [show V.conjBy x=V.map (MulAut.conj x).toMonoidHom from rfl,
      ←map_equiv_normalizer_eq V (MulAut.conj x)]
    have hh:=map_mono (f:=(MulAut.conj x).toMonoidHom) hNV
    have he:N.map (MulAut.conj x).toMonoidHom=N:=mem_normalizer_iff_map_conj_eq.mp (show x∈normalizer (N:Set G) from hxN)
    rwa [he] at hh
  have hNI:N≤normalizer (I:Set G):=by
    apply (le_inf (inf_le_left.trans (c.sylow_lt.le.trans hTZ))
      ((le_inf hNV hNVx).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hxI:x∈normalizer (I:Set G):=by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change I.conjBy x=I
    have hZ:Z.conjBy x=Z:=mem_normalizer_iff_map_conj_eq.mp (hTZ hxT)
    have hVV:(V.conjBy x).conjBy x=V:=by
      rw [conjBy_conjBy,←pow_two]
      exact mem_normalizer_iff_map_conj_eq.mp hx2
    change (Z⊔(V⊔V.conjBy x)).map (MulAut.conj x).toMonoidHom=I
    rw [Subgroup.map_sup,Subgroup.map_sup]
    change Z.conjBy x⊔(V.conjBy x⊔(V.conjBy x).conjBy x)=I
    rw [hZ,hVV,sup_comm (V.conjBy x) V]
  have hUI:U≤normalizer (I:Set G):=sup_le hNI (zpowers_le.mpr hxI)
  have hUT:U≤c.T:=sup_le (inf_le_left.trans c.sylow_lt.le) (zpowers_le.mpr hxT)
  have hNb:N∈beta M:=MathieuSourceSetup.plane_normalizer_mem_beta c hG V hVY hRV hcore hi
  have hUb:U∈beta M:=beta_mono hNb le_sup_left (c.T.isPGroup'.to_le hUT)
  have hzI:z∈I:=mem_sup_left (mem_zpowers z)
  have hz1:z≠1:=by intro he;have hh:=c.involution;rw [he,orderOf_one] at hh;omega
  have hIe:I∈Chapter1.S2e G:=by
    apply Chapter1.lemma_1_1_4_3 c.T (hG.evenCharacteristic c.T)
      (fun he=>hz1 (mem_bot.mp (show z∈(⊥:Subgroup G) from he ▸ hzI)))
      ((S.isPGroup'.map H.subtype).to_le hIY)
    intro he
    exact hz1 (mem_bot.mp (show z∈(⊥:Subgroup G) from he ▸ (show z∈(center (c.T:Subgroup G)).map (c.T:Subgroup G).subtype⊓I from ⟨c.mem_center,hzI⟩)))
  have hQ:twoCore (normalizer (I:Set G))≠⊥:=by
    intro he
    exact hIe.1 (bot_unique (he ▸ le_pCoreIn_of_normalizes hIe.2.1 I.le_normalizer le_rfl))
  have hnot:¬normalizer (I:Set G)≤M:=fun h=>hout (hXI.trans h)
  apply gammaZero_large_local_base_false c.gamma hempty
    (show (U,normalizer (I:Set G))∈localPairs (Chapter1.He G) M from ⟨hUb,hIe.2.2,hQ,hUI,hnot⟩)
  rw [←sylow_image_card H S]
  exact card_le_adjoin_of_relIndex_le_two N Y inf_le_left hi x hxS

theorem MathieuSourceSetup.exists_square_moving_crossing_plane
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    {κ:GroupClass} (hG:IsSimpleQTKE κ G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (V X:Subgroup G)
    (hVR:V≤elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))
    (hRV:elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)≤normalizer (V:Set G))
    (hcore:twoCore H≤normalizer (V:Set G))
    (hi:((S:Subgroup H).map H.subtype⊓normalizer (V:Set G)).relIndex ((S:Subgroup H).map H.subtype)≤2)
    (hcent:elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓centralizer (V:Set G)≤V⊔twoCore H)
    (hVX:V≤X) (hXL:X≤L) (hXV:X≤normalizer (V:Set G)) (hout:¬X≤M)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hx:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype)
    (hcross:V.conjBy x≤centralizer (V:Set G)) :
    ∃y:G,y∈c.T ∧ y∉(S:Subgroup H).map H.subtype ∧
      y∈normalizer ((S:Subgroup H).map H.subtype:Set G) ∧
      y^2∈(S:Subgroup H).map H.subtype ∧ y^2∉normalizer (V:Set G) := by
  let Y:=(S:Subgroup H).map H.subtype
  let R:=elementaryAbelianMaxJ Y
  let N:=Y⊓normalizer (V:Set G)
  by_cases hs:x^2∈normalizer (V:Set G)
  · by_cases hn:x∈normalizer (N:Set G)
    · have hxR:x∈normalizer (R:Set G):=by
        apply mem_normalizer_iff_map_conj_eq.mpr
        have hh:Y.map (MulAut.conj x).toMonoidHom=Y:=mem_normalizer_iff_map_conj_eq.mp hx
        change R.map (MulAut.conj x).toMonoidHom=R
        rw [←elementaryAbelianMaxJ_map_injective _ (MulAut.conj x).injective,hh]
      exact False.elim (MathieuSourceSetup.invariant_crossing_plane_false c hG hempty hgen
        V X hVR hRV hcore hi hcent hVX hXL hXV hout x hxT hxS hxR hn hs hcross)
    · obtain ⟨y,hyT,hyS,hy,hy2,hyn⟩:=exists_square_escape_of_moved_subgroup N Y c.T
        inf_le_left c.sylow_lt.le x hxT hxS hx hx2 hn
      exact ⟨y,hyT,hyS,hy,hy2,fun h=>hyn ⟨hy2,h⟩⟩
  · exact ⟨x,hxT,hxS,hx,hx2,hs⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
