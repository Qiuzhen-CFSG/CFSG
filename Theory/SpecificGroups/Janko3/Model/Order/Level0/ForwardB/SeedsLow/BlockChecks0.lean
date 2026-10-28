module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.BlockData

/-! Kernel certificates for four-letter products, batch 0. See BlockData. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem block0_spec : ∀ x : Fin 6156,
    lookup packed0 x.val = (evalWord gen [0] x).val := by
  have h : ∀ x : Fin 6156, lookup packed0 x.val = ev rawGen [0] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block1_spec : ∀ x : Fin 6156,
    lookup packed1 x.val = (evalWord gen [0, 1, 0, 1] x).val := by
  have h : ∀ x : Fin 6156, lookup packed1 x.val = ev rawGen [0, 1, 0, 1] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block2_spec : ∀ x : Fin 6156,
    lookup packed2 x.val = (evalWord gen [0, 1, 0, 3] x).val := by
  have h : ∀ x : Fin 6156, lookup packed2 x.val = ev rawGen [0, 1, 0, 3] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block3_spec : ∀ x : Fin 6156,
    lookup packed3 x.val = (evalWord gen [0, 1, 0, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed3 x.val = ev rawGen [0, 1, 0, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block4_spec : ∀ x : Fin 6156,
    lookup packed4 x.val = (evalWord gen [0, 1, 0, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed4 x.val = ev rawGen [0, 1, 0, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block5_spec : ∀ x : Fin 6156,
    lookup packed5 x.val = (evalWord gen [0, 1, 0, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed5 x.val = ev rawGen [0, 1, 0, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block6_spec : ∀ x : Fin 6156,
    lookup packed6 x.val = (evalWord gen [0, 1, 4, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed6 x.val = ev rawGen [0, 1, 4, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block7_spec : ∀ x : Fin 6156,
    lookup packed7 x.val = (evalWord gen [0, 1, 4, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed7 x.val = ev rawGen [0, 1, 4, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block8_spec : ∀ x : Fin 6156,
    lookup packed8 x.val = (evalWord gen [0, 1, 5, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed8 x.val = ev rawGen [0, 1, 5, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block9_spec : ∀ x : Fin 6156,
    lookup packed9 x.val = (evalWord gen [0, 1, 5, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed9 x.val = ev rawGen [0, 1, 5, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block10_spec : ∀ x : Fin 6156,
    lookup packed10 x.val = (evalWord gen [0, 1, 6, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed10 x.val = ev rawGen [0, 1, 6, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block11_spec : ∀ x : Fin 6156,
    lookup packed11 x.val = (evalWord gen [0, 3] x).val := by
  have h : ∀ x : Fin 6156, lookup packed11 x.val = ev rawGen [0, 3] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block12_spec : ∀ x : Fin 6156,
    lookup packed12 x.val = (evalWord gen [0, 3, 0] x).val := by
  have h : ∀ x : Fin 6156, lookup packed12 x.val = ev rawGen [0, 3, 0] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block13_spec : ∀ x : Fin 6156,
    lookup packed13 x.val = (evalWord gen [0, 3, 0, 1] x).val := by
  have h : ∀ x : Fin 6156, lookup packed13 x.val = ev rawGen [0, 3, 0, 1] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block14_spec : ∀ x : Fin 6156,
    lookup packed14 x.val = (evalWord gen [0, 3, 0, 3] x).val := by
  have h : ∀ x : Fin 6156, lookup packed14 x.val = ev rawGen [0, 3, 0, 3] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block15_spec : ∀ x : Fin 6156,
    lookup packed15 x.val = (evalWord gen [0, 3, 0, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed15 x.val = ev rawGen [0, 3, 0, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block16_spec : ∀ x : Fin 6156,
    lookup packed16 x.val = (evalWord gen [0, 3, 0, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed16 x.val = ev rawGen [0, 3, 0, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block17_spec : ∀ x : Fin 6156,
    lookup packed17 x.val = (evalWord gen [0, 3, 0, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed17 x.val = ev rawGen [0, 3, 0, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block18_spec : ∀ x : Fin 6156,
    lookup packed18 x.val = (evalWord gen [0, 3, 4, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed18 x.val = ev rawGen [0, 3, 4, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
