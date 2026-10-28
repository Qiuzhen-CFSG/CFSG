module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Native
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.PointSmallOpposite
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardAttachment
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCorePairingTransport
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpaceTransport

/-!
# Compatible paired intersections for the full point-core branch

At critical distance four, the strict reverse Baumann slice makes the actual
intersection of the moved subgroup and neighboring full seed have order
strictly less than sixteen. In the order-thirty-two core coordinates it
contains the radical fixed space and is radical invariant. The finite
point-core pairing theorem therefore supplies one even actor and its inverse,
retaining the original critical transposition and both generation identities.

The constant-vector intersection pulls back to the ambient center. Central
generation of the full omega layer then restores its central factor, giving
both full-seed central triples. Each prescribed actor yields its own strict
backward critical path with the literal first edge and all overlapping
vertices. The known-simple application discharges cover size, strictness and
central generation, and constructs a critical path with central forward
triple on the original free-amalgam graph.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6) and (5.12), printed pp.919--920,924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative Pointwise commutatorElement
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
namespace PointSmallCompatible
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

private theorem cover_paired_intersection
    (h32 : Nat.card (replacementMoved d) = 32) (u t : S)
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    (ht : t.IsSwap) (htR : t ∈ d.radical.map s.projection)
    (H : Subgroup d.overgroup) (hHU : H ≤ replacementMoved d)
    (hHcard : Nat.card H < 16)
    (hfix : replacementMoved d ⊓ centralizer (d.radical : Set d.overgroup) ≤ H)
    (hnorm : d.radical ≤ normalizer (H : Set d.overgroup)) :
    ∃ g ∈ replacementComponent d,
      ((d.radical.map s.projection).map (MulAut.conj (s.projection g)).toMonoidHom ⊔
        zpowers t = ⊤) ∧
      ((d.radical.map s.projection).map (MulAut.conj (s.projection g⁻¹)).toMonoidHom ⊔
        zpowers t = ⊤) ∧
      H ⊓ H.map (MulAut.conj g).toMonoidHom ≤ center d.overgroup ∧
      H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom ≤ center d.overgroup := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le hHU
  let σ := coverAction s
  let W := NormalElementaryQuotient.subgroupSpace U H
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  obtain ⟨E,hE⟩ : ∃ E : Additive U ≃ₗ[ZMod 2] core (Fin 6),
      ∀ k v, E (σ k v) = coreRepresentation (Fin 6) k (E v) := by
    rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
    · have h16 : Nat.card (replacementMoved d) = 16 := by
        change Nat.card (Additive U) = 16
        rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
          finrank_natural_even (Fin 6) (by decide)]
        norm_num
      omega
    · exact ⟨E,hE⟩
  let V := W.map E.toLinearMap
  have hVsmall : Nat.card V < 16 := by
    have hWV : Nat.card V ≤ Nat.card W :=
      Nat.card_le_card_of_surjective
        (fun w : W => (⟨E w.val,⟨w.val,w.property,rfl⟩⟩ : V))
        (by rintro ⟨v,w,hw,rfl⟩; exact ⟨⟨w,hw⟩,rfl⟩)
    have hWH : Nat.card W = Nat.card H :=
      (Nat.card_congr (NormalElementaryQuotient.subgroupSpaceEquiv U H hHU).toEquiv).symm
    exact hWV.trans_lt (hWH.symm ▸ hHcard)
  have hVfixed : fixedSpace (coreRepresentation (Fin 6))
      (pointCore.map (MulAut.conj u).toMonoidHom) ≤ V := by
    intro x hx
    obtain ⟨v,rfl⟩ := E.surjective x
    refine ⟨v,?_,rfl⟩
    apply hfix
    refine ⟨v.toMul.property,?_⟩
    apply (NormalElementaryQuotient.mem_fixedSpace_image U s.projection s.surjective hker d.radical v).mp
    intro k
    apply E.injective
    change E (σ k.val v) = E v
    rw [hE]
    exact hx ⟨k,hfull ▸ k.property⟩
  have hVinv : ∀ r ∈ pointCore.map (MulAut.conj u).toMonoidHom,
      ∀ x ∈ V, coreRepresentation (Fin 6) r x ∈ V := by
    intro r hr x hx
    obtain ⟨g,hg,rfl⟩ := hfull.symm ▸ hr
    obtain ⟨v,hv,rfl⟩ := hx
    change coreRepresentation (Fin 6) (s.projection g) (E v) ∈ V
    rw [←hE]
    refine ⟨σ (s.projection g) v,?_,rfl⟩
    change ((σ (s.projection g) v).toMul : d.overgroup) ∈ H
    rw [coverAction_conjugate]
    exact (mem_normalizer_iff.mp (hnorm hg) _).mp hv
  obtain ⟨k,hkp,hkm,hWp,hWm⟩ := PointCorePairing.exists_paired_conjugate_card
    u t ht (hfull ▸ htR) V hVsmall hVfixed hVinv
  have hkL : k.val ∈ (replacementComponent d).map s.projection := by
    rw [s.component_image]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  have central (y : d.overgroup)
      (hy : ∀ x ∈ V ⊓ V.map (coreRepresentation (Fin 6) (s.projection y)),
        ∀ r : S, coreRepresentation (Fin 6) r x = x) :
      H ⊓ H.map (MulAut.conj y).toMonoidHom ≤ center d.overgroup := by
    rintro x ⟨hx,hm⟩
    let v : Additive U := Additive.ofMul ⟨x,hHU hx⟩
    have hv : E v ∈ V := ⟨v,hx,rfl⟩
    obtain ⟨a,ha,he⟩ := hm
    let w : Additive U := Additive.ofMul ⟨a,hHU ha⟩
    have hmove : σ (s.projection y) w = v := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (coverAction_conjugate s y w).trans he
    have hvm : E v ∈ V.map (coreRepresentation (Fin 6) (s.projection y)) :=
      ⟨E w,⟨w,ha,rfl⟩,by rw [←hE,hmove]⟩
    apply mem_center_iff.mpr
    intro b
    have hh := E.injective ((hE (s.projection b) v).trans (hy _ ⟨hv,hvm⟩ _))
    have heq := congrArg (fun z : Additive U => (z.toMul : d.overgroup)) hh
    rw [coverAction_conjugate] at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  refine ⟨g,hg,?_,?_,?_,?_⟩
  · simpa only [hfull,hgk] using hkp
  · simpa only [hfull,map_inv,hgk] using hkm
  · apply central
    simpa only [hgk] using hWp
  · apply central
    simpa only [map_inv,hgk] using hWm


private theorem central_factor_triple {M : Type*} [Group M]
    (U Z V : Subgroup M) (hUZ : U ≤ Z) (hZ : Z ≤ U ⊔ center M)
    (hCV : Z ⊓ center M ≤ V) (g : M)
    (hUn : g ∈ normalizer (U : Set M))
    (hpair : (U ⊓ V) ⊓ (U ⊓ V).map (MulAut.conj g).toMonoidHom ≤ center M) :
    V ⊓ Z ⊓ V.map (MulAut.conj g).toMonoidHom ≤ center M := by
  rintro x ⟨⟨hxV,hxZ⟩,hxg⟩
  obtain ⟨w,hw,c,hc,rfl⟩ := mem_sup_of_normal_right.mp (hZ hxZ)
  have hcZ : c ∈ Z := by
    have hh := Z.mul_mem (Z.inv_mem (hUZ hw)) hxZ
    simpa only [inv_mul_cancel_left] using hh
  have hcV := hCV ⟨hcZ,hc⟩
  have hwV : w ∈ V := by
    have hh := V.mul_mem hxV (V.inv_mem hcV)
    simpa only [mul_inv_cancel_right] using hh
  have hcg : c ∈ V.map (MulAut.conj g).toMonoidHom := by
    refine ⟨c,hcV,?_⟩
    change g*c*g⁻¹=c
    rw [(mem_center_iff.mp hc g),mul_inv_cancel_right]
  have hwg : w ∈ V.map (MulAut.conj g).toMonoidHom := by
    have hh := (V.map (MulAut.conj g).toMonoidHom).mul_mem hxg
      ((V.map (MulAut.conj g).toMonoidHom).inv_mem hcg)
    simpa only [mul_inv_cancel_right] using hh
  have hwUg : w ∈ (U ⊓ V).map (MulAut.conj g).toMonoidHom := by
    have he : U.map (MulAut.conj g).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp hUn
    rw [Subgroup.map_inf U V (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,he]
    exact ⟨hw,hwg⟩
  exact (center M).mul_mem (hpair ⟨⟨hw,hwV⟩,hwUg⟩) hc

include h in
private theorem central_attachment_le_neighbor
    (_hc : DistanceTwo.CentralLayer d)
    {v : Vertex d.radical} (hv : color d.radical v = false)
    (hvb : Adjacent d.radical v (beta d.radical)) :
    Z d.radical (alpha d.radical) ⊓
      centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ≤
      Z d.radical v := by
  apply le_trans _ (adjacent_Z_le d.radical hv hvb)
  intro x hx
  have hXa : Z d.radical (alpha d.radical) ≤ X d.radical (alpha d.radical) := by
    apply (replacementGeometry h d).omega_bound _ rfl
    exact replacementDistance_pos h d
  obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp (hXa hx.1)
  rw [Z,if_neg (by change ¬ (true = false); decide)]
  refine mem_omegaCenter_iff.mpr ⟨?_,hx2,?_⟩
  · exact Q_le_adjacent_h d.radical (show color d.radical (beta d.radical)=true from rfl)
      (base_adjacent d.radical) hxQ
  · intro y hy
    exact hx.2 y (hy.2 _ (adjacent_symm d.radical (base_adjacent d.radical)))

/-- Pair both conjugates of the actual neighboring seed. The finite cover
calculation retains the original critical transposition and full attachment. -/
theorem full_point_paired_source_intersections
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (h32 : Nat.card (replacementMoved d)=32) (u : S)
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hgen : X d.radical (alpha d.radical) = U d.radical (alpha d.radical) ⊔
      (X d.radical (alpha d.radical) ⊓ centralizer
        (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))))
    (hstrict : 2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (alpha d.radical))) :
    let V := (Z d.radical (p.walk.getVert 2)).comap (embedM d.radical)
    let Z₀ := (Z d.radical (alpha d.radical)).comap (embedM d.radical)
    let A := (Z d.radical z).comap (embedM d.radical)
    ∃ g ∈ replacementComponent d,
      d.radical.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ ∧
      d.radical.map (MulAut.conj g⁻¹).toMonoidHom ⊔ A = ⊤ ∧
      V ⊓ Z₀ ⊓ V.map (MulAut.conj g).toMonoidHom ≤ center d.overgroup ∧
      V ⊓ Z₀ ⊓ V.map (MulAut.conj g⁻¹).toMonoidHom ≤ center d.overgroup := by
  let f := embedM d.radical
  let V := (Z d.radical (p.walk.getVert 2)).comap f
  let Z₀ := (Z d.radical (alpha d.radical)).comap f
  let A := (Z d.radical z).comap f
  let U₀ := replacementMoved d
  let H := U₀ ⊓ V
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hv : color d.radical (p.walk.getVert 2)=false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hvb : Adjacent d.radical (p.walk.getVert 2) (beta d.radical) := by
    rw [←hfirst]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hUmap : U₀.map f = U d.radical (alpha d.radical) := hc.U_eq_moved.symm
  have hZrange : Z d.radical (alpha d.radical) ≤ f.range :=
    (Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical)
  have hZmap : Z₀.map f = Z d.radical (alpha d.radical) := map_comap_eq_self hZrange
  have hHmap : H.map f = U d.radical (alpha d.radical) ⊓ Z d.radical (p.walk.getVert 2) := by
    rw [Subgroup.map_inf U₀ V f (embedM_injective d.radical),hUmap,map_comap_eq]
    have hUr : U d.radical (alpha d.radical) ≤ f.range := by
      rw [←hUmap]
      exact map_le_range f U₀
    rw [←inf_assoc,inf_eq_left.mpr hUr]
  have hHU : H ≤ U₀ := inf_le_left
  have hHcard : Nat.card H < 16 := by
    let T := H.map f
    let := finite_Z d.radical (alpha d.radical)
    let : Finite (U d.radical (alpha d.radical)) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical _)) (inclusion_injective _)
    have hTB : T ≤ B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _) :=
      (hHmap.le.trans inf_le_right).trans (Escape.EdgeTransfer.Z_le_B hb2 _ hv)
    have hi : 2 < T.relIndex (U d.radical (alpha d.radical)) :=
      hstrict.trans_le (relIndex_le_of_le_left hTB index_ne_zero_of_finite)
    have hTU : T ≤ U d.radical (alpha d.radical) := hHmap.le.trans inf_le_left
    have hcard : Nat.card T * T.relIndex (U d.radical (alpha d.radical)) = 32 := by
      have hh := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical))
        T (U d.radical (alpha d.radical)) bot_le hTU
      simp only [relIndex_bot_left] at hh
      rw [Nat.card_congr (graphMovedEquiv hc).toEquiv,h32] at hh
      exact hh
    have he : Nat.card H = Nat.card T :=
      Nat.card_congr (H.equivMapOfInjective f (embedM_injective d.radical)).toEquiv
    rw [he]
    nlinarith
  have hfix : U₀ ⊓ centralizer (d.radical : Set d.overgroup) ≤ H := by
    rintro x ⟨hx,hxc⟩
    refine ⟨hx,?_⟩
    apply adjacent_Z_le d.radical hv hvb
    rw [Z,if_neg (by change ¬ (true = false); decide)]
    have hX : f x ∈ X d.radical (alpha d.radical) :=
      (DistanceEight.U_le_Z d.radical _).trans
        ((replacementGeometry h d).omega_bound _ rfl (replacementDistance_pos h d))
        (hUmap ▸ mem_map_of_mem f hx)
    obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp hX
    refine mem_omegaCenter_iff.mpr ⟨?_,hx2,?_⟩
    · rw [Q_beta]
      exact mem_map_of_mem f ((replacement_core_le_radical h d)
        ((mem_omegaCenterIn_iff _ _).mp (replacementMoved_le_omegaCenter h d hx)).1)
    · intro y hy
      rw [Q_beta] at hy
      obtain ⟨r,hr,rfl⟩ := hy
      simpa only [map_mul] using congrArg f (hxc r hr)
  have hnorm : d.radical ≤ normalizer (H : Set d.overgroup) := by
    intro r hr
    have hrb : f r ∈ Q d.radical (beta d.radical) := by
      rw [Q_beta]
      exact mem_map_of_mem f hr
    have hrG : f r ∈ stabilizer d.radical (p.walk.getVert 2) :=
      hrb.2 _ (adjacent_symm d.radical hvb)
    have hnV : r ∈ normalizer (V : Set d.overgroup) := by
      apply mem_normalizer_iff.mpr
      intro x
      have hh := mem_normalizer_iff.mp (Z_normalized d.radical _ hrG) (f x)
      simpa only [V,mem_comap,map_mul,map_inv] using hh
    exact inf_normalizer_le_normalizer_inf
      ⟨by let := replacementMoved_normal h d; rw [normalizer_eq_top]; trivial,hnV⟩
  have hf : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hfull
  have hsmall := (full_point_four_critical_indices_two_knownSimple hb u hf p).1
  obtain ⟨t,htA,ht⟩ := small_critical_image_swap s hc p (by omega)
  have hAR : A ≤ d.radical := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [←Q_beta,←hfirst]
    apply (map_comap_le _ _).trans
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant z p.end_color]
    change p.walk.length-1 < replacementDistance h d
    omega
  obtain ⟨g,hg,hgp,hgm,hHp,hHm⟩ := cover_paired_intersection s h32 u t hfull ht
    (map_mono hAR htA) H hHU hHcard hfix hnorm
  have generation (y : d.overgroup)
      (hy : (d.radical.map s.projection).map (MulAut.conj (s.projection y)).toMonoidHom ⊔
        zpowers t = ⊤) : d.radical.map (MulAut.conj y).toMonoidHom ⊔ A = ⊤ := by
    have hm : (d.radical.map (MulAut.conj y).toMonoidHom).map s.projection =
        (d.radical.map s.projection).map (MulAut.conj (s.projection y)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change s.projection (y*x*y⁻¹) = s.projection y*s.projection x*(s.projection y)⁻¹
      simp only [map_mul,map_inv]
    have hQ : (pCore 2 d.overgroup).map (MulAut.conj y).toMonoidHom = pCore 2 d.overgroup :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; trivial)
    have hk : s.projection.ker ≤ d.radical.map (MulAut.conj y).toMonoidHom := by
      rw [s.projection_kernel,←hQ]
      exact map_mono (replacement_core_le_radical h d)
    apply map_injective_of_ker_le s.projection (hk.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hm,map_top_of_surjective s.projection s.surjective]
    apply top_unique
    rw [←hy]
    exact sup_le_sup_left (zpowers_le.mpr htA) _
  have hUZ : U₀ ≤ Z₀ := by
    intro x hx
    exact DistanceEight.U_le_Z d.radical _ (hUmap ▸ mem_map_of_mem f hx)
  have hZsup : Z₀ ≤ U₀ ⊔ center d.overgroup := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [Subgroup.map_sup,hUmap,hZmap]
    have hXZ : X d.radical (alpha d.radical) = Z d.radical (alpha d.radical) := by
      apply le_antisymm
      · rw [hgen]
        refine sup_le (DistanceEight.U_le_Z d.radical _) ?_
        apply le_trans _ (adjacent_Z_le d.radical rfl (base_adjacent d.radical))
        intro x hx
        rw [Z,if_neg (by change ¬ (true = false); decide)]
        obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp hx.1
        exact mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h d.radical rfl
          (base_adjacent d.radical) hxQ,hx2,
          fun y hy => hx.2 y (hy.2 _ (adjacent_symm d.radical (base_adjacent d.radical)))⟩
      · exact (replacementGeometry h d).omega_bound _ rfl (replacementDistance_pos h d)
    rw [←hXZ,hgen]
    refine sup_le le_sup_left (le_trans ?_ le_sup_right)
    intro x hx
    obtain ⟨y,hy⟩ := hZrange (hXZ ▸ hx.1)
    refine ⟨y,?_,hy⟩
    apply mem_center_iff.mpr
    intro r
    apply embedM_injective d.radical
    have hrG : f r ∈ stabilizer d.radical (alpha d.radical) := by
      change f r ∈ stabilizer d.radical (mVertex d.radical 1)
      rw [stabilizer_m_base]
      exact ⟨r,rfl⟩
    change f (r*y) = f (y*r)
    simpa only [map_mul,hy] using hx.2 (f r) hrG
  have hCV : Z₀ ⊓ center d.overgroup ≤ V := by
    rintro x ⟨hx,hxc⟩
    apply central_attachment_le_neighbor (h := h) hc hv hvb
    refine ⟨hx,?_⟩
    intro y hy
    change y ∈ stabilizer d.radical (mVertex d.radical 1) at hy
    rw [stabilizer_m_base] at hy
    obtain ⟨r,rfl⟩ := hy
    simpa only [map_mul] using congrArg f (mem_center_iff.mp hxc r)
  have hnU (y : d.overgroup) : y ∈ normalizer (U₀ : Set d.overgroup) := by
    let := replacementMoved_normal h d
    rw [normalizer_eq_top]
    trivial
  exact ⟨g,hg,generation g hgp,generation g⁻¹ hgm,
    central_factor_triple U₀ Z₀ V hUZ hZsup hCV g (hnU g) hHp,
    central_factor_triple U₀ Z₀ V hUZ hZsup hCV g⁻¹ (hnU _) hHm⟩


/-- Both prescribed finite actors lift to strict backward paths, each with
the central full-seed triple at the original starting vertex. -/
theorem full_point_paired_backward_intersections
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (h32 : Nat.card (replacementMoved d)=32) (u : S)
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hgen : X d.radical (alpha d.radical) = U d.radical (alpha d.radical) ⊔
      (X d.radical (alpha d.radical) ⊓ centralizer
        (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))))
    (hforward : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hreverse : 2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (alpha d.radical))) :
    ∃ g ∈ Ltilde d.radical (alpha d.radical),
      ∀ y ∈ ({g,g⁻¹} : Set (FreeAmalgam d.radical)),
        let c := act d.radical y (p.walk.getVert 2)
        let t := act d.radical y (beta d.radical)
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        Z d.radical (p.walk.getVert 2) ⊓ Z d.radical (alpha d.radical) ⊓ Z d.radical c ≤
          centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
          q.walk.getVert 1=t ∧
          ∀ i ≤ 2, q.walk.getVert (i+2)=p.walk.getVert i := by
  let f := embedM d.radical
  let V := (Z d.radical (p.walk.getVert 2)).comap f
  let Z₀ := (Z d.radical (alpha d.radical)).comap f
  let A := (Z d.radical z).comap f
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hv : color d.radical (p.walk.getVert 2)=false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hvb : Adjacent d.radical (p.walk.getVert 2) (beta d.radical) := by
    rw [←hfirst]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hf : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hfull
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [(full_point_four_critical_indices_two_knownSimple hb u hf p).1]
    decide
  obtain ⟨g,hg,hgp,hgm,hcp,hcm⟩ := full_point_paired_source_intersections s hc hb
    h32 u hfull p hfirst hgen hreverse
  have hL (y : d.overgroup) (hy : y ∈ replacementComponent d) :
      (f y)⁻¹ ∈ Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
    exact ⟨y⁻¹,inv_mem hy,map_inv f y⟩
  refine ⟨(f g)⁻¹,hL g hg,?_⟩
  have one (y : d.overgroup) (hy : y ∈ replacementComponent d)
      (hygen : d.radical.map (MulAut.conj y).toMonoidHom ⊔ A = ⊤)
      (hycentral : V ⊓ Z₀ ⊓ V.map (MulAut.conj y).toMonoidHom ≤ center d.overgroup) :
      let c := act d.radical (f y)⁻¹ (p.walk.getVert 2)
      let t := act d.radical (f y)⁻¹ (beta d.radical)
      Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
      Z d.radical (p.walk.getVert 2) ⊓ Z d.radical (alpha d.radical) ⊓ Z d.radical c ≤
        centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
        q.walk.getVert 1=t ∧ ∀ i ≤ 2, q.walk.getVert (i+2)=p.walk.getVert i := by
    let c := act d.radical (f y)⁻¹ (p.walk.getVert 2)
    let t := act d.radical (f y)⁻¹ (beta d.radical)
    have hyG : (f y)⁻¹ ∈ stabilizer d.radical (alpha d.radical) :=
      Ltilde_le_stabilizer _ (hL y hy)
    have hya : act d.radical (f y)⁻¹ (alpha d.radical) = alpha d.radical := hyG
    have hat : Adjacent d.radical (alpha d.radical) t := by
      rw [←hya]
      exact (adjacent_act_iff d.radical _ _ _).mpr (base_adjacent d.radical)
    have hct : Adjacent d.radical c t := (adjacent_act_iff d.radical _ _ _).mpr hvb
    have hcol : color d.radical c = false := by
      rw [action_preserves_color]
      exact hv
    have map_conj (J : Subgroup d.overgroup) :
        (J.map (MulAut.conj y).toMonoidHom).map f =
        (J.map f).map (MulAut.conj (f y)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f (y*x*y⁻¹) = f y*f x*(f y)⁻¹
      simp only [map_mul,map_inv]
    have hAm : A.map f = Z d.radical z := map_comap_eq_self
      ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
        (replacementDistance_pos h d) p.critical).trans_eq (stabilizer_m_base d.radical))
    have hZm : Z₀.map f = Z d.radical (alpha d.radical) := map_comap_eq_self
      ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
    have hVm : V.map f = Z d.radical (p.walk.getVert 2) := by
      apply map_comap_eq_self
      have hZQ : Z d.radical (p.walk.getVert 2) ≤ Q d.radical (alpha d.radical) := by
        apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ hv)
        rw [(replacementGeometry h d).distance_constant _ hv,SimpleGraph.dist_comm,p.dist_start (by omega)]
        exact hb2
      have hQr : Q d.radical (alpha d.radical) ≤ f.range := by
        intro x hx
        have hxG := hx.1
        change x ∈ stabilizer d.radical (mVertex d.radical 1) at hxG
        rwa [stabilizer_m_base] at hxG
      exact hZQ.trans hQr
    have hgent : Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) := by
      have hh := congrArg (Subgroup.map f) hygen
      rw [Subgroup.map_sup,map_conj,hAm,←Q_beta,←MonoidHom.range_eq_map] at hh
      change (Q d.radical (act d.radical (f y)⁻¹ (beta d.radical)) ⊔ _) = _
      rw [Q_act,inv_inv]
      exact hh.trans (stabilizer_m_base d.radical).symm
    have hcentral : Z d.radical (p.walk.getVert 2) ⊓ Z d.radical (alpha d.radical) ⊓ Z d.radical c ≤
        centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
      have hh := map_mono (f := f) hycentral
      rw [Subgroup.map_inf _ _ f (embedM_injective d.radical),Subgroup.map_inf _ _ f (embedM_injective d.radical),
        map_conj,hVm,hZm] at hh
      change _ ≤ _
      rw [Z_act,inv_inv]
      apply hh.trans
      rintro x ⟨a,ha,rfl⟩ b hb
      change b ∈ stabilizer d.radical (mVertex d.radical 1) at hb
      rw [stabilizer_m_base] at hb
      obtain ⟨b,rfl⟩ := hb
      simpa only [map_mul] using congrArg f (mem_center_iff.mp ha b)
    have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj (f y)).toMonoidHom =
        B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
      apply mem_normalizer_iff_map_conj_eq.mp
      exact Escape.Propagation.Rigidity.B_normalized hb2 _ rfl (by simpa only [inv_inv] using inv_mem hyG)
    have hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) := by
      change 2 < (B d.radical _ _).relIndex (U d.radical (act d.radical (f y)⁻¹ _))
      rw [U_act,inv_inv,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hforward
    refine ⟨hgent,hcentral,hstrict,?_⟩
    have hbad := small_image_backward_not_le s hc hb2 u hfull.le p hsmall hat hct hgent hstrict
    let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length = 2 := rfl
    let q := p.prepend_two (Nat.le_of_lt hb2) hcol w hw hbad
    have hq1 : q.walk.getVert 1 = t := by
      simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,hw,
        show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]
    have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
    let q' : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2) := {
      start_color := q.start_color
      walk := q.walk.copy rfl he
      shortest := by rw [SimpleGraph.Walk.length_copy,q.shortest,he]
      critical := by simpa only [he] using q.critical }
    refine ⟨q',?_,?_⟩
    · change (q.walk.copy rfl he).getVert 1 = t
      rwa [SimpleGraph.Walk.getVert_copy]
    · intro i hi
      change (q.walk.copy rfl he).getVert (i+2) = p.walk.getVert i
      rw [SimpleGraph.Walk.getVert_copy]
      exact p.prepend_two_overlap _ _ _ _ _ (by omega)
  intro y hy
  rcases Set.mem_insert_iff.mp hy with rfl | hy
  · exact one g hg hgp hcp
  · obtain rfl := Set.mem_singleton_iff.mp hy
    dsimp only
    rw [←map_inv f g]
    exact one g⁻¹ (inv_mem hg) hgm hcm



include e hz hn in
theorem full_point_paired_backward_intersections_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) = pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hfirst : p.walk.getVert 1 = beta d.radical)
 :
    ∃ g ∈ Ltilde d.radical (alpha d.radical),
      ∀ y ∈ ({g,g⁻¹} : Set (FreeAmalgam d.radical)),
        let c := act d.radical y (p.walk.getVert 2)
        let t := act d.radical y (beta d.radical)
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        Z d.radical (p.walk.getVert 2) ⊓ Z d.radical (alpha d.radical) ⊓ Z d.radical c ≤
          centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
          q.walk.getVert 1=t ∧
          ∀ i ≤ 2, q.walk.getVert (i+2)=p.walk.getVert i := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have h32 : Nat.card (replacementMoved d)=32 := by
    rcases moved_card s with h16 | h32
    · exact False.elim (distance_ne_four_of_natural_full_point s h16 u hf hb)
    · exact h32
  have hgen := full_point_omega_centrally_generated_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull (alpha d.radical) rfl
  have hforward := (full_point_all_slices_strict_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull p).1
  let r : CriticalPath d.radical (replacementGeometry h d) z (alpha d.radical) :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  have hreverse := (full_point_all_slices_strict_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull r).2
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hrm : r.walk.getVert 2 = p.walk.getVert 2 := by
    change p.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hl]
  rw [hrm] at hreverse
  exact full_point_paired_backward_intersections s hc hb h32 u hf p hfirst hgen hforward hreverse

include e hz hn in
/-- The literal full point-core source supplies a critical path whose full
endpoint-seed triple is central at its midpoint. -/
theorem full_point_exists_central_critical_path_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ a z : Vertex d.radical,
      ∃ p : CriticalPath d.radical (replacementGeometry h d) a z,
        Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
          centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hadj : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 0) (by omega))
  obtain ⟨k,hk⟩ := edge_transitive d.radical hadj (base_adjacent d.radical)
  have he : act d.radical k (alpha d.radical) = alpha d.radical ∧
      act d.radical k (p.walk.getVert 1) = beta d.radical := by
    rcases hk with hk | hk
    · exact hk
    · have hh := congrArg (color d.radical) hk.1
      rw [action_preserves_color] at hh
      contradiction
  have base := full_point_paired_backward_intersections_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull (z := act d.radical k z)
  rw [←he.1] at base
  have hfirst : (p.act k).walk.getVert 1 = beta d.radical := by
    change (actWalk d.radical k p.walk).getVert 1 = _
    rw [actWalk_getVert,he.2]
  obtain ⟨g,hg,hgpair⟩ := base (p.act k) hfirst
  obtain ⟨_,hcentral,_,q,_,hover⟩ := hgpair g (by simp)
  have hqm : q.walk.getVert 2 = act d.radical k (alpha d.radical) := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  refine ⟨_,_,q,?_⟩
  rw [hqm]
  rintro x ⟨⟨hxc,hxa⟩,hxv⟩
  exact hcentral ⟨⟨hxv,hxa⟩,hxc⟩

end PointSmallCompatible
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
