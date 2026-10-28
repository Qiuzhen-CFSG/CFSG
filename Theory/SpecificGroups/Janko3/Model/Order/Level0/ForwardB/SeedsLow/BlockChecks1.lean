module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.BlockData

/-! Kernel certificates for four-letter products, batch 1. See BlockData. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem block19_spec : ∀ x : Fin 6156,
    lookup packed19 x.val = (evalWord gen [0, 3, 4, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed19 x.val = ev rawGen [0, 3, 4, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block20_spec : ∀ x : Fin 6156,
    lookup packed20 x.val = (evalWord gen [0, 3, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed20 x.val = ev rawGen [0, 3, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block21_spec : ∀ x : Fin 6156,
    lookup packed21 x.val = (evalWord gen [0, 3, 5, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed21 x.val = ev rawGen [0, 3, 5, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block22_spec : ∀ x : Fin 6156,
    lookup packed22 x.val = (evalWord gen [0, 3, 5, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed22 x.val = ev rawGen [0, 3, 5, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block23_spec : ∀ x : Fin 6156,
    lookup packed23 x.val = (evalWord gen [0, 3, 6, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed23 x.val = ev rawGen [0, 3, 6, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block24_spec : ∀ x : Fin 6156,
    lookup packed24 x.val = (evalWord gen [0, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed24 x.val = ev rawGen [0, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block25_spec : ∀ x : Fin 6156,
    lookup packed25 x.val = (evalWord gen [0, 4, 4, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed25 x.val = ev rawGen [0, 4, 4, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block26_spec : ∀ x : Fin 6156,
    lookup packed26 x.val = (evalWord gen [0, 4, 5, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed26 x.val = ev rawGen [0, 4, 5, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block27_spec : ∀ x : Fin 6156,
    lookup packed27 x.val = (evalWord gen [0, 4, 5, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed27 x.val = ev rawGen [0, 4, 5, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block28_spec : ∀ x : Fin 6156,
    lookup packed28 x.val = (evalWord gen [0, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed28 x.val = ev rawGen [0, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block29_spec : ∀ x : Fin 6156,
    lookup packed29 x.val = (evalWord gen [0, 5, 4, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed29 x.val = ev rawGen [0, 5, 4, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block30_spec : ∀ x : Fin 6156,
    lookup packed30 x.val = (evalWord gen [0, 5, 4, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed30 x.val = ev rawGen [0, 5, 4, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block31_spec : ∀ x : Fin 6156,
    lookup packed31 x.val = (evalWord gen [0, 5, 6, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed31 x.val = ev rawGen [0, 5, 6, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block32_spec : ∀ x : Fin 6156,
    lookup packed32 x.val = (evalWord gen [0, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed32 x.val = ev rawGen [0, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block33_spec : ∀ x : Fin 6156,
    lookup packed33 x.val = (evalWord gen [0, 6, 5, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed33 x.val = ev rawGen [0, 6, 5, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block34_spec : ∀ x : Fin 6156,
    lookup packed34 x.val = (evalWord gen [0, 6, 5, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed34 x.val = ev rawGen [0, 6, 5, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block35_spec : ∀ x : Fin 6156,
    lookup packed35 x.val = (evalWord gen [1] x).val := by
  have h : ∀ x : Fin 6156, lookup packed35 x.val = ev rawGen [1] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block36_spec : ∀ x : Fin 6156,
    lookup packed36 x.val = (evalWord gen [1, 0] x).val := by
  have h : ∀ x : Fin 6156, lookup packed36 x.val = ev rawGen [1, 0] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block37_spec : ∀ x : Fin 6156,
    lookup packed37 x.val = (evalWord gen [1, 0, 1] x).val := by
  have h : ∀ x : Fin 6156, lookup packed37 x.val = ev rawGen [1, 0, 1] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
